module GRIN.Analysis.Effects

import Data.List
import Data.List1
import Data.SortedMap as Map

import GRIN.AST
import GRIN.GrinState

filter : (a -> Bool) -> List1 a -> List a
filter pred = filter pred . forget

data PartialResult : Type -> Type where
    Cond : List1 name -> PartialResult name
    Definite : Effectful -> PartialResult name

Semigroup (PartialResult name) where
    Cond xs <+> Cond ys = Cond $ xs ++ ys
    Definite NoEffect <+> e = e
    Definite Effect <+> e = Definite Effect
    e <+> Definite NoEffect = e
    e <+> Definite Effect = Definite Effect

Monoid (PartialResult name) where
    neutral = Definite NoEffect

parameters {auto _ : Eq name} (env : SortedMap name (PartialResult name)) (current : name)
  mutual
    effectSExp : SExp name -> PartialResult name
    effectSExp (Do x) = effectExp x
    effectSExp (App x xs) = case lookup x env of
        Nothing => Cond (singleton x)
        Just (Cond xs) => case filter (/= current) xs of
            [] => Definite NoEffect
            (x :: xs) => Cond $ x ::: xs
        Just eff@(Definite _) => eff
    effectSExp (Pure x) = Definite NoEffect
    effectSExp (Store x) = Definite NoEffect
    effectSExp (Fetch x y) = Definite NoEffect
    effectSExp (FetchI x k y) = Definite NoEffect
    effectSExp (Update x y) = Definite Effect

    effectExp : Exp name -> PartialResult name
    effectExp (SimpleExp e) = effectSExp e
    effectExp (Bind _ rhs rest) = effectSExp rhs <+> effectExp rest
    effectExp (Case _ alts) = foldMap effectAlt alts

    effectAlt : Alt name -> PartialResult name
    effectAlt (MkAlt _ exp) = effectExp exp

effectDef : Eq name => SortedMap name (PartialResult name) -> Def name -> PartialResult name
effectDef env def = effectExp env def.defName def.body

addExternToEnv : SortedMap name (PartialResult name) -> Extern name -> SortedMap name (PartialResult name)
addExternToEnv env ext = insert ext.extName (Definite ext.eff) env

addDefToEnv : Eq name => SortedMap name (PartialResult name) -> Def name -> SortedMap name (PartialResult name)
addDefToEnv env def = insert def.defName (effectDef env def) env
