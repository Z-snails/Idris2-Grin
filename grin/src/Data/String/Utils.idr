module Data.String.Utils

import Data.List

indentSize : Nat
indentSize = 4

export
parens : String -> String
parens b = "(" ++ b ++ ")"

export
bracket : String -> String
bracket b = "[" ++ b ++ "]"

export
indent : Nat -> String -> String
indent n b = fastConcat (replicate (n * indentSize) " ") ++ b

export
function : Show fun => Show arg => fun -> List arg -> String
function f args = show f ++ fastConcat ((\arg => " " ++ show arg) <$> args)

export
nlSep : Show a => List a -> String
nlSep xs = fastConcat $ (\x => show x ++ "\n\n") <$> xs
