module GRIN.Optimisations.SimpleCopyPropogation

import Data.SortedMap

import Compiler.Pipeline

import GRIN.Syntax

CopyMap : Type
CopyMap = SortedMap GrinVar GrinVar

isValVar : Val -> Maybe GrinVar
isValVar (VSimpleVal (SVar var)) = Just var
isValVar _ = Nothing

isPureVar : SimpleExp -> Maybe GrinVar
isPureVar (Pure val) = isValVar val
isPureVar _ = Nothing

copyPropVar : CopyMap -> GrinVar -> GrinVar
copyPropVar cm var = case lookup var cm of
    Nothing => var
    Just var' => var'

copyPropSVal : CopyMap -> SimpleVal -> SimpleVal
copyPropSVal _ (SLit lit) = SLit lit
copyPropSVal cm (SVar var) = SVar (copyPropVar cm var)
copyPropSVal _ (SUndefined ty) = SUndefined ty

copyPropVal : CopyMap -> Val -> Val
copyPropVal cm (VTagNode tag args) = VTagNode tag (copyPropSVal cm <$> args)
copyPropVal _ (VTag tag) = VTag tag
copyPropVal cm (VSimpleVal val) = VSimpleVal (copyPropSVal cm val)
copyPropVal _ VUnit = VUnit

mutual
    copyPropSExp : CopyMap -> SimpleExp -> SimpleExp
    copyPropSExp cm (Do exp) = Do (copyPropExp cm exp)
    copyPropSExp cm (App var vars) = App var (copyPropVar cm <$> vars)
    copyPropSExp cm (Pure val) = Pure (copyPropVal cm val)
    copyPropSExp cm (Store val) = Store (copyPropVal cm val)
    copyPropSExp cm (Fetch var) = Fetch (copyPropVar cm var)
    copyPropSExp cm (Update var val) = Update (copyPropVar cm var) (copyPropVal cm val)

    copyPropExp : CopyMap -> GrinExp -> GrinExp
    copyPropExp cm (Bind val rhs rest) =
        let rhs' = copyPropSExp cm rhs in
        case isValVar val of
            Nothing => Bind val rhs' (copyPropExp cm rest)
            Just copy => case isPureVar rhs of
                Nothing => Bind val rhs' (copyPropExp cm rest)
                Just var => copyPropExp (insert copy var cm) rest
    copyPropExp cm (Case val alts) = Case (copyPropVal cm val) (copyPropAlt cm <$> alts)
    copyPropExp cm (Simple exp) = Simple (copyPropSExp cm exp)

    copyPropAlt : CopyMap -> GrinAlt -> GrinAlt
    copyPropAlt cm (MkAlt pat exp) = MkAlt pat (copyPropExp cm exp)

copyPropDef : GrinDef -> GrinDef
copyPropDef (MkDef n args exp) = MkDef n args (copyPropExp empty exp)

copyPropProg : GrinProg -> GrinProg
copyPropProg (MkProg exts defs) = MkProg exts (copyPropDef <$> defs)

export
simpleCopyPropogation : TransInfo (\x => x) GrinProg GrinProg
simpleCopyPropogation = MkTI \prog => copyPropProg prog