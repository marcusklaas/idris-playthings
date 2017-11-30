data Format =
    Literal String Format |
    IntegerArgument Format |
    StringArgument Format |
    End

toFormat : String -> Format
toFormat template = inspect (unpack template) where
      inspect : List Char -> Format
      inspect ('%' :: 's' :: xs) = StringArgument $ inspect xs
      inspect ('%' :: 'd' :: xs) = IntegerArgument $ inspect xs
      inspect (x :: xs) = case inspect xs of
                            Literal lit fmtCont => Literal (pack . (x ::) . unpack $ lit) fmtCont
                            fmt => Literal (pack (x :: Nil)) fmt
      inspect Nil = End

PrintType : Format -> Type
PrintType (Literal str fmt) = PrintType fmt
PrintType (IntegerArgument fmt) = Int -> (PrintType fmt)
PrintType (StringArgument fmt) = String -> (PrintType fmt)
PrintType End = String

printWithBuffer : (template: Format) -> String -> PrintType template
printWithBuffer (Literal lit fmt) buf = printWithBuffer fmt (buf ++ lit)
printWithBuffer (IntegerArgument fmt) buf = \i => printWithBuffer fmt (buf ++ show i)
printWithBuffer (StringArgument fmt) buf = \s => printWithBuffer fmt (buf ++ s)
printWithBuffer End buf = buf

printf : (template : String) -> PrintType (toFormat template)
printf template = printWithBuffer (toFormat template) ""
