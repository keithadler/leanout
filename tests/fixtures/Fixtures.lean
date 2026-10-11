/-
Copyright 2026 Keith Adler
Licensed under the Apache License, Version 2.0 (see LICENSE).

Declarations that exercise every corner of the export format.
-/
universe u v

-- mutual inductives
mutual
inductive Even : Nat → Prop
  | zero : Even 0
  | succ : Odd n → Even (n + 1)
inductive Odd : Nat → Prop
  | succ : Even n → Odd (n + 1)
end

mutual
inductive Tree (α : Type u) where
  | node : α → Forest α → Tree α
inductive Forest (α : Type u) where
  | nil : Forest α
  | cons : Tree α → Forest α → Forest α
end

-- nested inductive (auxiliary rec_N recursors)
inductive Rose (α : Type u) where
  | mk : α → List (Rose α) → Rose α

inductive Rose2 where
  | mk : Array Rose2 → Option Rose2 → Rose2

-- reflexive inductive, indexed family, universe-polymorphic structure
inductive Reflexive where
  | mk : (Nat → Reflexive) → Reflexive

inductive Vec (α : Type u) : Nat → Type u where
  | nil : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)

structure Pair (α : Type u) (β : Type v) where
  fst : α
  snd : β
  deriving Repr

structure Dep where
  n : Nat
  v : Vec Nat n
  h : n = n := rfl

-- structural eta, projections, let, literals
def big : Nat := 2 ^ 200 + 123456789012345678901234567890
def msg : String := "héllo ∀ wörld \x41"
def etaPair (p : Pair Nat Nat) : Pair Nat Nat := ⟨p.1, p.2⟩
theorem etaPair_eq (p : Pair Nat Nat) : etaPair p = p := rfl
def withLet (n : Nat) : Nat := let m := n + 1; let k := m * 2; k + m
theorem big_pos : 0 < big := by decide

-- quotients
def Mod3 := Quot (fun a b : Nat => a % 3 = b % 3)
def Mod3.mk (n : Nat) : Mod3 := Quot.mk _ n
def Mod3.val : Mod3 → Nat := Quot.lift (· % 3) (fun _ _ h => h)

-- well-founded and structural recursion, universe levels with max/imax
def ack : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)
termination_by m n => (m, n)

def pi (α : Sort u) (β : α → Sort v) : Sort (imax u v) := (a : α) → β a
def mx (α : Type u) (β : Type v) : Type (max u v) := α × β

-- classical axioms
theorem em' (p : Prop) : p ∨ ¬p := Classical.em p

-- these must be skipped by default
partial def loopForever (n : Nat) : Nat := loopForever (n + 1)
unsafe def unsafeId (n : Nat) : Nat := n
