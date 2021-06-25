module GRIN.Opts.Inline

import Data.SortedMap
import Data.List

import GRIN.AST
import GRIN.GrinM
import GRIN.Var

mutual
    elimFetchIdSExp : SExp name -> SExp name
    elimFetchIdSExp (Do e) = mkDo $ elimFetchIdExp e
    elimFetchIdSExp (Fetch _ v) = fetch v
    elimFetchIdSExp (FetchI _ i v) = fetchI i v
    elimFetchIdSExp e = e

    elimFetchIdExp : Exp name -> Exp name
    elimFetchIdExp = mapSExpExp elimFetchIdSExp

mutual
    inlineSExp : MonadVar m => SortedMap name (Def name) -> SExp name -> m (SExp name)
    inlineSExp im (Do e) = mkDo <$> inlineExp im e
    inlineSExp im (App fn as) = case lookup fn im of
        Nothing => pure $ App fn as
        Just (MkDef _ as' e0 _) => do
            putVars $ fromList $ zip as' as
            e1 <- updateVars e0
            e2 <- inlineExp im e1
            pure $ mkDo e2
    inlineSExp im e = pure e

    inlineExp : MonadVar m => SortedMap name (Def name) -> Exp name -> m (Exp name)
    inlineExp im (SimpleExp e) = mkSimpleExp <$> inlineSExp im e
    inlineExp im (Bind val rhs rest) = Bind val <$> inlineSExp im rhs <*> inlineExp im rest
    inlineExp im (Case pat alts) = Case pat <$> traverse (inlineAlt im) alts

    inlineAlt : MonadVar m => SortedMap name (Def name) -> Alt name -> m (Alt name)
    inlineAlt im (MkAlt pat e) = MkAlt pat <$> inlineExp im e

inlineDef : MonadVar m => SortedMap name (Def name) -> Def name -> m (Def name)
inlineDef im (MkDef fn as exp ty) = MkDef fn as <$> (inlineExp im exp) <*> pure ty

export
inlineAll : Monad m => GrinT name m ()
inlineAll = do
    im <- gets toInline
    if null im
        then pure ()
        else do
            MkProg exts defs m <- gets prog
            defs' <- traverse (inlineDef im) defs
            modify $ record { prog = MkProg exts defs' m }
            invalidate CallGraphs
