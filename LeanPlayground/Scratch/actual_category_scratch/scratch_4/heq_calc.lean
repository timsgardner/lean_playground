/-! # `HEq` in `calc`

`calc` reads the two sides of a relation off the last two arguments of its application.
That works for `Eq {α} a b`, but `HEq {α} a {β} b` ends with `β` and `b`, so `calc` takes
the type `β` for the left-hand side. `HEqR` is `HEq` with the two types moved to the
front, so that its last two arguments are the two sides and `calc` can chain it. -/

/-- `HEq a b`, with arguments ordered so that `calc` can use it. -/
def HEqR {α β : Sort u} (a : α) (b : β) : Prop := HEq a b

@[inherit_doc] infix:50 " ≍ᵣ " => HEqR

theorem HEqR.symm {α β : Sort u} {a : α} {b : β} (h : a ≍ᵣ b) : b ≍ᵣ a := HEq.symm h

theorem HEqR.toHEq {α β : Sort u} {a : α} {b : β} (h : a ≍ᵣ b) : HEq a b := h

instance {α β γ : Sort u} : Trans (@HEqR α β) (@HEqR β γ) (@HEqR α γ) :=
  ⟨fun h₁ h₂ => HEq.trans h₁ h₂⟩

instance {α β : Sort u} : Trans (@Eq α) (@HEqR α β) (@HEqR α β) :=
  ⟨fun h₁ h₂ => h₁ ▸ h₂⟩

instance {α β : Sort u} : Trans (@HEqR α β) (@Eq β) (@HEqR α β) :=
  ⟨fun h₁ h₂ => h₂ ▸ h₁⟩
