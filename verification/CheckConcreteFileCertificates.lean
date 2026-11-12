import ConcreteFileCertificates

def main : IO Unit :=
  IO.print (String.ofList PegHs.ConcreteFileCertificates.firstTopItem)
