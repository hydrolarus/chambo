{
module Parsing where

import Syntax
import Data.Char
}

%name parseFile
%tokentype { Token }
%error { parseError }

%token
    function        { TokenFunction    }
    requires        { TokenRequires    }
    ensures         { TokenEnsures     }
    assert          { TokenAssert      }
    forall          { TokenForall      }
    exists          { TokenExists      }
    let             { TokenLet         }
    in              { TokenIn          }
    if              { TokenIf          }
    then            { TokenThen        }
    else            { TokenElse        }

    int             { TokenInt $$      }
    string          { TokenString $$   }
    bool            { TokenBool $$     }
    unit            { TokenUnit        }

    ident           { TokenIdent $$    }

    '+'             { TokenPlus        }
    '-'             { TokenMinus       }
    '*'             { TokenAsterisk    }
    '/'             { TokenSlash       }
    '='             { TokenEqual       }
    '!='            { TokenNotEqual    }
    '<'             { TokenLt          }
    '<='            { TokenLte         }
    '>'             { TokenGt          }
    '>='            { TokenGte         }
    '==>'           { TokenImplies     }
    '&&'            { TokenAnd         }
    '||'            { TokenOr          }
    
    '!'             { TokenNot         }

    '\\/'           { TokenDisjunction }
    '/\\'           { TokenConjunction }

    '{'             { TokenBraceOpen   }
    '}'             { TokenBraceClose  }
    '('             { TokenParenOpen   }
    ')'             { TokenParenClose  }

    ';'             { TokenSemicolon   }
    ':'             { TokenColon       }
    '.'             { TokenDot         }
    ','             { TokenComma       }

    'int'           { TokenIntType     }
    'string'        { TokenStringType  }
    'bool'          { TokenBoolType    }

%right in
%right else
%right ';'
%right '==>'
%nonassoc '=' '!='
%left '||'
%left '&&'
%nonassoc '<' '<=' '>' '>='
%left '+' '-'
%left '*' '/'
-- %left NOT


%%

File : Items { File $1 }

Items : {- empty -}    { [] }
      | Function Items { (IFunction $1) : $2 }

Function    : function ident '(' FuncDeclArgs ')'
                ':' Type
                Preconditions
                Postconditions
                '=' Expr              { Function $2 $4 $7 $8 $9 $11 Nothing }

FuncDeclArgs : {- empty -}         { [] }
             | ident ':' Type      { [($1, $3)] }
             | ident ':' Type ','  { [($1, $3)] }
             | ident ':' Type ',' FuncDeclArgs { ($1, $3) : $5 }

Preconditions : {- empty -}     { [] }
              | requires '{' Term '}' Preconditions { $3 : $5 }

Postconditions : {- empty -}     { [] }
               | ensures '{' Term '}' Postconditions { $3 : $5 }



Expr    : let ident '=' Expr in Expr  { ELet $2 $4 $6 }
        | Expr '+' Expr               { EBinOp OpAdd $1 $3 }
        | Expr '-' Expr               { EBinOp OpSub $1 $3 }
        | Expr '*' Expr               { EBinOp OpMul $1 $3 }
        | Expr '/' Expr               { EBinOp OpDiv $1 $3 }
        | Expr '=' Expr               { EBinOp OpEq $1 $3 }
        | Expr '!=' Expr              { EBinOp OpNeq $1 $3 }
        | Expr '<' Expr               { EBinOp OpLt $1 $3 }
        | Expr '<=' Expr              { EBinOp OpLte $1 $3 }
        | Expr '>' Expr               { EBinOp OpGt $1 $3 }
        | Expr '>=' Expr              { EBinOp OpGte $1 $3 }
        | Expr '==>' Expr             { EBinOp OpImplies $1 $3 }
        | Expr '&&' Expr              { EBinOp OpAnd $1 $3 }
        | Expr '||' Expr              { EBinOp OpOr $1 $3 }
        | '!' Expr                    { EPrefixOp OpNot $2 }
        | '(' Expr ')'                { $2 }
        | Expr ';' Expr               { ESeq $1 $3 }

        | if Expr then Expr else Expr { EIf $2 $4 $6}

        | ident '(' FuncCallArgs ')'  { EFunCall $1 $3 }

        | int                         { EIntLiteral $1 }
        | string                      { EStringLiteral $1 }
        | bool                        { EBoolLiteral $1 }
        | '(' ')'                     { EUnitLiteral }

        | ident                       { EVar $1 }
        | assert '{' Term '}'         { EAssert $3 }

Term    : Expr                           { TExpr $1 Nothing }
        | forall ident ':' Type '.' Term { TForall $2 $4 $6 }
        | Term '\\/' Term                { TDisjunction $1 $3 }
        | Term '/\\' Term                { TConjunction $1 $3 }

Type    : 'int'     { TInt    }
        | 'string'  { TString }
        | 'bool'    { TBool   }
        | '(' ')'   { TUnit   }


FuncCallArgs : {- empty -}         { [] }
             | ident ':' Expr      { [($1, $3)] }
             | ident ':' Expr ','  { [($1, $3)] }
             | ident ':' Expr ',' FuncCallArgs { ($1, $3) : $5 }
{

parseError :: [Token] -> a
parseError toks = error $ "parse error, rest: " ++ show toks

data Token
    = TokenFunction
    | TokenRequires
    | TokenEnsures
    | TokenAssert
    | TokenForall
    | TokenExists
    | TokenLet
    | TokenIn
    | TokenIf
    | TokenThen
    | TokenElse
    | TokenInt Integer
    | TokenString String
    | TokenBool Bool
    | TokenUnit
    | TokenIdent String
    | TokenPlus
    | TokenMinus
    | TokenAsterisk
    | TokenSlash
    | TokenEqual
    | TokenNotEqual
    | TokenLt
    | TokenLte
    | TokenGt
    | TokenGte
    | TokenImplies
    | TokenAnd
    | TokenOr
    | TokenNot
    | TokenDisjunction 
    | TokenConjunction 
    | TokenBraceOpen
    | TokenBraceClose
    | TokenParenOpen
    | TokenParenClose
    | TokenSemicolon
    | TokenColon
    | TokenDot
    | TokenComma
    | TokenIntType
    | TokenStringType
    | TokenBoolType
    deriving (Show)


lexer :: String -> [Token]
lexer [] = []
lexer (c:cs)
    | isSpace c = lexer cs
    | isAlpha c = lexIdent (c:cs)
    | isDigit c = lexNumber (c:cs)
lexer ('/':'/':cs) = lexer (dropWhile (/= '\n') cs)
lexer ('\\':'/':cs) = TokenDisjunction : lexer cs
lexer ('/':'\\':cs) = TokenConjunction : lexer cs
lexer ('+':cs) = TokenPlus : lexer cs
lexer ('-':cs) = TokenMinus : lexer cs
lexer ('*':cs) = TokenAsterisk : lexer cs
lexer ('/':cs) = TokenSlash : lexer cs
lexer ('!':'=':cs) = TokenNotEqual : lexer cs
lexer ('<':'=':cs) = TokenLte : lexer cs
lexer ('<':cs) = TokenLt : lexer cs
lexer ('>':'=':cs) = TokenGte : lexer cs
lexer ('>':cs) = TokenGt : lexer cs
lexer ('=':'=':'>':cs) = TokenImplies : lexer cs
lexer ('&':'&':cs) = TokenAnd : lexer cs
lexer ('|':'|':cs) = TokenOr : lexer cs
lexer ('=':cs) = TokenEqual : lexer cs
lexer ('!':cs) = TokenNot : lexer cs
lexer ('{':cs) = TokenBraceOpen : lexer cs
lexer ('}':cs) = TokenBraceClose : lexer cs
lexer ('(':cs) = TokenParenOpen : lexer cs
lexer (')':cs) = TokenParenClose : lexer cs
lexer (';':cs) = TokenSemicolon : lexer cs
lexer (':':cs) = TokenColon : lexer cs
lexer ('.':cs) = TokenDot : lexer cs
lexer (',':cs) = TokenComma : lexer cs
lexer (c:cs) = error $ "Unexpected character " ++ show c

lexNumber :: String -> [Token]
lexNumber cs = TokenInt (read num) : lexer rest
      where (num, rest) = span isDigit cs

lexIdent :: String -> [Token]
lexIdent cs =
    case span (\c -> isAlphaNum c || c == '_' || c == '\'') cs of
        ("function", rest) -> TokenFunction : lexer rest
        ("requires", rest) -> TokenRequires : lexer rest
        ("ensures", rest) -> TokenEnsures : lexer rest
        ("assert", rest) -> TokenAssert : lexer rest
        ("forall", rest) -> TokenForall : lexer rest
        ("exists", rest) -> TokenExists : lexer rest
        ("let", rest) -> TokenLet : lexer rest
        ("in", rest)  -> TokenIn : lexer rest
        ("if", rest) -> TokenIf : lexer rest
        ("then", rest) -> TokenThen : lexer rest
        ("else", rest) -> TokenElse : lexer rest
        ("int", rest) -> TokenIntType : lexer rest
        ("string", rest) -> TokenStringType : lexer rest
        ("bool", rest) -> TokenBoolType : lexer rest

        ("true", rest) -> TokenBool True : lexer rest
        ("false", rest) -> TokenBool False : lexer rest

        (ident, rest)   -> TokenIdent ident : lexer rest

parse :: String -> File
parse s = parseFile $ lexer s
}