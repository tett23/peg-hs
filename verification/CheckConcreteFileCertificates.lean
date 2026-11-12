import ConcreteFileCertificates
import InitialWhitespace

def main (args : List String) : IO Unit :=
  match args with
  | [] => IO.print (String.ofList PegHs.ConcreteFileCertificates.firstTopItem)
  | ["syntax"] => IO.print (String.ofList PegHs.ConcreteFileCertificates.syntaxFirstTopItem)
  | ["whitespace"] => IO.print (String.ofList PegHs.MetaExecution.initialComments)
  | _ => throw (IO.userError "expected no argument, syntax or whitespace")
