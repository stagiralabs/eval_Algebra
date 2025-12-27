import Lake
open Lake DSL

package «eval_Algebra» {
  -- Package configuration
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.17.0"

require "leanprover-community" / "batteries" @ git "v4.17.0"

require "leanprover" / "Cli" @ git "v4.17.0"

require VerifiedAgora from git
  "https://github.com/stagiralabs/VerifiedAgora.git" @ "v4.17.0"

@[default_target]
lean_lib Targets where

lean_lib Library where
