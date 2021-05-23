module Data.String.Builder

import Data.Buffer
import Data.List

data BuilderTree : Int -> Type where
    Empty : BuilderTree 0
    Str : (str : String) -> BuilderTree (prim__strLength str)
    Seq : {a : Int} -> (BuilderTree a) -> (BuilderTree b) -> BuilderTree (a + b)

runBuilderTree : Buffer -> (off : Int) -> BuilderTree size -> IO ()
runBuilderTree b off Empty = pure ()
runBuilderTree b off (Str str) = setString b off str
runBuilderTree b off (Seq {a} l r) = runBuilderTree b off l *> runBuilderTree b (off + a) r

mapStringTree : (String -> String) -> BuilderTree _ -> (size ** BuilderTree size)
mapStringTree f Empty = (_ ** Empty)
mapStringTree f (Str str) = (_ ** Str (f str))
mapStringTree f (Seq l r) =
    let (sl ** l') = mapStringTree f l
        (sr ** r') = mapStringTree f r
    in (_ ** Seq l' r')

export
record Builder where
    constructor MkBuilder
    size : Int
    tree : BuilderTree size

export
runBuilder : Builder -> String
runBuilder (MkBuilder size tree) = unsafePerformIO $ do
    Just b <- newBuffer size
        | Nothing => pure ""
    runBuilderTree b 0 tree
    str <- getString b 0 size
    freeBuffer b
    pure str

export
mapString : (String -> String) -> Builder -> Builder
mapString f (MkBuilder _ t) =
    let (size ** tree) = mapStringTree f t
    in MkBuilder size tree

export
Semigroup Builder where
    MkBuilder s1 t1 <+> MkBuilder s2 t2 = MkBuilder (s1 + s2) (Seq t1 t2)

export
Monoid Builder where
    neutral = MkBuilder 0 Empty

export
FromString Builder where
    fromString str = if str == ""
        then neutral
        else MkBuilder (prim__strLength str) (Str str)

public export
interface ShowB a where
    showB : a -> Builder

export
[FromShow] Show a => ShowB a where
    showB = fromString . show

indentSize : Nat
indentSize = 4

export
parens : Builder -> Builder
parens b = "(" <+> b <+> ")"

export
bracket : Builder -> Builder
bracket b = "[" <+> b <+> "]"

export
indent : Nat -> Builder -> Builder
indent n b = fromString (fastConcat $ replicate (n * indentSize) " ") <+> b

export
function : ShowB fun => ShowB arg => Foldable t => fun -> t arg -> Builder
function f args = showB f <+> foldMap (\arg => " " <+> showB arg) args

export
nlSep : ShowB a => Foldable t => t a -> Builder
nlSep xs = foldMap (\x => showB x <+> "\n\n") xs

export
nl1Sep : ShowB a => Foldable t => t a -> Builder
nl1Sep xs = foldMap (\x => "\n" <+> showB x) xs <+> "\n"
