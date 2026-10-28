import Mathlib.Init
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic

-- Vec for idiots like me
def Voc (α : Type) : ℕ → Type
| 0 => Unit
| n + 1 => α × Voc α n
