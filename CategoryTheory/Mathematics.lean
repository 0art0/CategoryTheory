import CategoryTheory.Basics

structure Monoid where
  U : Type _
  op : U → U → U
  e : U

  opAssoc : ∀ a b c : U, op (op a b) c = op a (op b c)
  leftId : ∀ a : U, op e a = a
  rightId : ∀ a : U, op a e = a

structure Group extends Monoid where
  inv : U → U

  leftInv : ∀ a : U, op (inv a) a = e
  rightInv : ∀ a : U, op a (inv a) = e

open CategoryTheory in
def MonoidCategory (M : Monoid) : Category :=
  {
    ob := Unit,
    hom := λ _ _ => M.U,
    id := M.e,
    comp := M.op,

    compAssoc := by intros; simp [M.opAssoc],
    leftId := by intros; simp [M.leftId],
    rightId := by intros; simp [M.rightId]
  }

open CategoryTheory in
def GroupCategory (G : Group) : Category :=
  {
    ob := Unit,
    hom := λ _ _ => G.U,
    id := G.e,
    comp := G.op,

    compAssoc := by intros; simp [G.opAssoc],
    leftId := by intros; simp [G.leftId],
    rightId := by intros; simp [G.rightId]
  }

structure Poset where
  P : Type _
  rel : P → P → Bool

  refl : ∀ {a : P}, rel a a
  antisymm : ∀ {a b : P}, rel a b → rel b a → a = b
  trans : ∀ {a b c : P}, rel a b → rel b c → rel a c

open CategoryTheory in
def Δ : Category :=
  {
    ob := Σ n : Nat, Fin (Nat.succ n)
    hom := λ ⟨m, fₘ⟩ ⟨n, fₙ⟩ => {ϕ : Fin m.succ → Fin n.succ // ∀ {a b}, a ≤ b → ϕ a ≤ ϕ b},
    id := ⟨id, id⟩,
    comp := λ ⟨f, prf⟩ ⟨g, prg⟩ => ⟨g ∘ f, prg ∘ prf⟩,

    compAssoc := by intros; rfl,
    leftId := by intros; rfl,
    rightId := by intros; rfl
  }

namespace CategoryTheory


/-
def PosetCategory (PO : Poset) : Category :=
  {
    ob := PO.P,
    hom := PO.rel,
    id := PO.refl,
    comp := PO.trans,

    compAssoc := by intros; rfl,
    leftId := by intros; rfl,
    rightId := by intros; rfl
  }

def POSet : Category :=
  {
    ob := Poset,
    hom := λ P Q => {f : P.P → Q.P // ∀ {p p' : P.P}, P.rel p p' → Q.rel (f p) (f p')},
    id := ⟨id, id⟩,
    comp := λ ⟨f, prf⟩ ⟨g, prg⟩ => ⟨g ∘ f, prg ∘ prf⟩,

    compAssoc := by intros; simp; rfl,
    leftId := by intros; simp; rfl,
    rightId := by intros; simp; rfl
  }
-/



end CategoryTheory
