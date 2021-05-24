module GRIN.Parser

import Control.Monad.State
import Data.String.Parser

import GRIN.AST

%hide Data.String.Parser.space
%hide Data.String.Parser.spaces
%hide Data.String.Parser.lexeme
%hide Data.String.Parser.Parser

Parser : Type -> Type
Parser = ParseT (State Nat)

MonadState Nat Parser where
    get = lift get
    put = lift . put
    state = lift . state

space : Parser Char
space = char ' '

newlines : Parser ()
newlines =
    ignore $ many
        (satisfy (\c => c == '\n' || c == '\r') <?> "newline")

pVar : Parser Var
pVar = char 'v' *> (MkVar . cast <$> integer)

pRef : Parser String
pRef = takeWhile isAlpha

pTagType : Parser TagType
pTagType = choice
    [ Con <$ char 'C'
    , Partial <$ char 'P' <*> natural
    , NUThunk <$ string "FNU"
    , UThunk <$ char 'F'
    , UThunk <$ string "FU"
    ]

pTag : Parser (Tag String)
pTag = [| MkTag pTagType (takeWhile isAlphaNum) |]

pLit : Parser Lit
pLit = choice
    [ LInt . cast <$> integer
    ]

pIntPrec : Parser IntPrec
pIntPrec = optional (string "T_") *> choice
    [ Signed <$ string "Int" <*> natural
    , Unsigned <$ string "Word" <*> natural
    ]


