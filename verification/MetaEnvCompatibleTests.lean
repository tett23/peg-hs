import MetaEnvCompatible

open PegHs.EnvRunCongruence PegHs.MetaEnvCompatible PegHs.MetaExecution

example (input : List Char) : Compatible (context false input) :=
  actual_context_compatible false input

example (input : List Char) : Compatible (context true input) :=
  actual_context_compatible true input
