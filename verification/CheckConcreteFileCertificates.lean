import ConcreteFileCertificates

def main (args : List String) : IO Unit :=
  match args with
  | [] => IO.print (String.ofList PegHs.ConcreteFileCertificates.firstTopItem)
  | ["syntax"] => IO.print (String.ofList PegHs.ConcreteFileCertificates.syntaxFirstTopItem)
  | _ => throw (IO.userError "expected no argument or syntax")
