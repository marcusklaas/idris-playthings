data Format =
    StringLiteral String Format |
    Integery Format |
    Stringy Format |
    End

toFormat : String -> Format
toFormat template = inspect (unpack template) where
      inspect : List Char -> Format
      inspect ('%' :: 's' :: xs) = Stringy $ inspect xs
      inspect ('%' :: 'd' :: xs) = Integery $ inspect xs
      inspect (x :: xs) = case inspect xs of
                            StringLiteral lit fmtCont => StringLiteral (pack . (x ::) . unpack $ lit) fmtCont
                            fmt => StringLiteral (pack (x :: Nil)) fmt
      inspect Nil = End

PrintType : Format -> Type
PrintType (StringLiteral str fmt) = PrintType fmt
PrintType (Integery fmt) = Int -> (PrintType fmt)
PrintType (Stringy fmt) = String -> (PrintType fmt)
PrintType End = String

printFormat : (template: Format) -> String -> PrintType template
printFormat (StringLiteral lit fmt) buf = printFormat fmt (buf ++ lit)
printFormat (Integery fmt) buf = \i => printFormat fmt (buf ++ show i)
printFormat (Stringy fmt) buf = \s => printFormat fmt (buf ++ s)
printFormat End buf = buf

printf : (template : String) -> PrintType (toFormat template)
printf template = printFormat (toFormat template) ""
