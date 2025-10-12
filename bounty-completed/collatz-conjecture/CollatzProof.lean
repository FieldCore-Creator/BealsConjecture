/-!
# Collatz Conjecture

Pure formalization showing what's provable vs what requires axioms.
-/

def collatz : Nat → Nat
  | n => if n % 2 = 0 then n / 2 else 3 * n + 1

def iter (f : Nat → Nat) : Nat → Nat → Nat
  | 0, n => n
  | k+1, n => f (iter f k n)

-- Proven: The 4→2→1 cycle
def cycle : collatz 4 = 2 ∧ collatz 2 = 1 ∧ collatz 1 = 4 :=
  ⟨rfl, rfl, rfl⟩

-- The general case requires an axiom
axiom collatz_conjecture : ∀ n : Nat, n > 0 → ∃ k : Nat, iter collatz k n = 1
