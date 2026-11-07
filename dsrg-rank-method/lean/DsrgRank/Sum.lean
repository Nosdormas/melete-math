

namespace DsrgRank

/-- `sumBelow n f = f 0 + … + f (n − 1)`. -/
def sumBelow : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n + 1, f => sumBelow n f + f n

theorem zo_bounds {a : Int} (h : a = 0 ∨ a = 1) : 0 ≤ a ∧ a ≤ 1 := by
  omega

theorem pair_facts {a b : Int} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    0 ≤ a * b ∧ a * b ≤ a ∧ a * b ≤ b ∧ a + b - a * b ≤ 1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

theorem add_scaled_le {a b c d : Int} (w : Int) (hw : 0 ≤ w) (h : a ≤ b) (acc : c ≤ d) :
    c + w * a ≤ d + w * b := by
  have := Int.mul_le_mul_of_nonneg_left h hw
  omega

theorem sumBelow_congr {n : Nat} {f g : Nat → Int} (h : ∀ l, l < n → f l = g l) :
    sumBelow n f = sumBelow n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumBelow]
    rw [ih (fun l hl => h l (by omega)), h n (by omega)]

theorem sumBelow_add (n : Nat) (f g : Nat → Int) :
    sumBelow n (fun l => f l + g l) = sumBelow n f + sumBelow n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sumBelow, ih]; omega

theorem sumBelow_sub (n : Nat) (f g : Nat → Int) :
    sumBelow n (fun l => f l - g l) = sumBelow n f - sumBelow n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sumBelow, ih]; omega

theorem sumBelow_mul_left (n : Nat) (c : Int) (f : Nat → Int) :
    sumBelow n (fun l => c * f l) = c * sumBelow n f := by
  induction n with
  | zero => simp [sumBelow]
  | succ n ih => simp only [sumBelow, ih, Int.mul_add]

theorem sumBelow_le {n : Nat} {f g : Nat → Int} (h : ∀ l, l < n → f l ≤ g l) :
    sumBelow n f ≤ sumBelow n g := by
  induction n with
  | zero => exact Int.le_refl _
  | succ n ih =>
    simp only [sumBelow]
    have := ih (fun l hl => h l (by omega))
    have := h n (by omega)
    omega

theorem sumBelow_single {n a : Nat} (c : Int) (ha : a < n) :
    sumBelow n (fun l => if l = a then c else 0) = c := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [sumBelow]
    by_cases e : a = n
    · subst e
      have : sumBelow a (fun l => if l = a then c else 0) = 0 := by
        rw [sumBelow_congr (g := fun _ => 0) (fun l hl => by simp; omega)]
        clear ha; induction a with
        | zero => rfl
        | succ m ihm => simp [sumBelow, ihm]
      simp [this]
    · rw [ih (by omega)]; simp [Ne.symm e]

end DsrgRank
