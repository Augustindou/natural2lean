import Lake
open Lake DSL

package LeanUtils {
  dependencies := #[{
    name := "mathlib",
    src := Source.git "https://github.com/leanprover-community/mathlib4.git" "9c01694fd1775fc5d50380debef5272c16d2196b"
  }]
}
