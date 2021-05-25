module GRIN.Opts.CopyPropogation

import Data.SortedMap

import GRIN.AST
import GRIN.GrinM

0 CopyMap : Type
CopyMap = SortedMap Var Var

isValVar : (Val name) -> Maybe Var
isValVar (SimpleVal (SVar var)) = Just var
isValVar _ = Nothing

isPureVar : SExp name -> Maybe Var
isPureVar (Pure val) = isValVar val
isPureVar _ = Nothing

copyPropVar : CopyMap -> Var -> Var
copyPropVar cm var = case lookup var cm of
    Nothing => var
    Just var' => var'

copyPropSVal : CopyMap -> SVal -> SVal
copyPropSVal _ (SLit lit) = SLit lit
copyPropSVal cm (SVar var) = SVar (copyPropVar cm var)

copyPropVal : CopyMap -> Val name -> Val name
copyPropVal cm (SimpleVal val) = SimpleVal (copyPropSVal cm val)
copyPropVal cm (ConstTagNode tag args) = ConstTagNode tag (copyPropSVal cm <$> args)
copyPropVal _ (ConstTag tag) = ConstTag tag
copyPropVal cm (VarTagNode var args) = VarTagNode var (copyPropSVal cm <$> args)
copyPropVal _ VUnit = VUnit

mutual
    copyPropSExp : CopyMap -> SExp name -> SExp name
    copyPropSExp cm (Do exp) = Do (copyPropExp cm exp)
    copyPropSExp cm (App fn vars) = App fn (copyPropVar cm <$> vars)
    copyPropSExp cm (Pure val) = Pure (copyPropVal cm val)
    copyPropSExp cm (Store val) = Store (copyPropVal cm val)
    copyPropSExp cm (Fetch i var) = Fetch i (copyPropVar cm var)
    copyPropSExp cm (FetchI i n var) = FetchI i n (copyPropVar cm var)
    copyPropSExp cm (Update var val) = Update (copyPropVar cm var) (copyPropVal cm val)

    copyPropExp : CopyMap -> Exp name -> Exp name
    copyPropExp cm (Bind val rhs rest) =
        let rhs' = copyPropSExp cm rhs in
        case isValVar val of
            Nothing => Bind val rhs' (copyPropExp cm rest)
            Just copy => case isPureVar rhs of
                Nothing => Bind val rhs' (copyPropExp cm rest)
                Just var => copyPropExp (insert copy var cm) rest
    copyPropExp cm (Case val alts) = Case (copyPropVal cm val) (copyPropAlt cm <$> alts)
    copyPropExp cm (SimpleExp exp) = SimpleExp (copyPropSExp cm exp)

    copyPropAlt : CopyMap -> Alt name -> Alt name
    copyPropAlt cm (MkAlt pat exp) = MkAlt pat (copyPropExp cm exp)

export
copyProp : Monad m => GrinT name m ()
copyProp = mapProg $ mapExpProg (copyPropExp empty)
