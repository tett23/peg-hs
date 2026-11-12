import Verbatim47Data

def main : IO Unit :=
  IO.print (String.ofList (['%', '{'] ++
    PegHs.MetaExecution.Verbatim47Data.suffix0 ++ ['\n', '\n']))
