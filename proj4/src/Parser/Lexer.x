{
module Parser.Lexer ( Token (..)
                    , lexProg ) where
}

%wrapper "basic"

$digit = 0-9
$alpha = [a-zA-Z]
$symb = [\_]

tokens:-
    $white+                             ;
    "if"                                { const TIf }
    "then"                              { const TThen }
    "else"                              { const TElse }
    "end"                               { const TEnd }
    "while"                             { const TWhile }
    "pre"                               { const TPre }
    "forall"                            { const TForall }
    "exists"                            { const TExists }
    "do"                                { const TDo }
    "program"                           { const TProgram }
    "is"                                { const TIs }
    "assert"                            { const TAssert}
    $digit+                             { TokenInt . read }
    $alpha [$alpha $digit $symb ]*      { TokenName }
    [\[ \] \+ \- \* \/ \% ]             { TokenSymb }
    [\( \) ]                            { TokenSymb }
    [\= \< \>]                          { TokenSymb }
    \!\=                                { TokenSymb }
    \>\=                                { TokenSymb }
    \<\=                                { TokenSymb }
    \!                                  { TokenSymb }
    \=\=\>                              { TokenSymb }
    \|\|                                { TokenSymb }
    \&\&                                { TokenSymb }
    \:\=                                { TokenSymb }
    \,                                  { TokenSymb }
    \;                                  { TokenSymb }
    
{
data Token = TokenInt Int
           | TokenName String
           | TokenSymb String
           | TIf
           | TThen
           | TElse
           | TEnd
           | TWhile
           | TPre
           | TForall
           | TExists
           | TDo
           | TProgram
           | TIs
           | TAssert
           deriving (Eq, Show)

lexProg :: String -> [Token]
lexProg = alexScanTokens

}
