-- Advanced pattern matching

-- Pattern matching with type ascription
def test1 : Sum Nat String → String
  | Sum.inl (n : Nat) => toString n
  | Sum.inr (s : String) => s

-- Dependent pattern matching
def replicate : (n : Nat) → α → Vector α n
  | 0, _ => Vector.nil
  | n + 1, x => Vector.cons x (replicate n x)

-- Pattern matching on proofs
def decidableEq : (x y : Nat) → Decidable (x = y)
  | 0, 0 => isTrue rfl
  | x + 1, y + 1 =>
    match decidableEq x y with
    | isTrue h => isTrue (by rw [h])
    | isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
  | 0, _ + 1 => isFalse (by intro h; cases h)
  | _ + 1, 0 => isFalse (by intro h; cases h)

-- View patterns (using auxiliary definitions)
def isJust : Option α → Bool
  | some _ => true
  | none => false

def fromJust : (o : Option α) → isJust o = true → α
  | some x, _ => x
  | none, h => False.elim (by simp [isJust] at h)

-- Pattern matching with motive
def Vector.head : {n : Nat} → Vector α (n + 1) → α
  | _, Vector.cons x _ => x

-- Match with explicit motive
def depMatch (n : Nat) : (match n with | 0 => Unit | _ => Nat) :=
  match n with
  | 0 => ()
  | n + 1 => n

-- Pattern matching on equality proofs
def transport {α : Type} {P : α → Type} {x y : α} 
    (h : x = y) (px : P x) : P y :=
  match h with
  | rfl => px

-- Absurd patterns
def emptyElim {α : Type} : Empty → α
  | e => match e with.

-- No confusion patterns
def injective_succ : {n m : Nat} → n + 1 = m + 1 → n = m
  | _, _, h => by
    cases h
    rfl

-- Pattern matching with universe polymorphism
def const.{u, v} {α : Type u} {β : Type v} (x : α) : β → α
  | _ => x

-- Structural recursion through patterns
def ackermann : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => ackermann m 1
  | m + 1, n + 1 => ackermann m (ackermann (m + 1) n)

-- Mutual recursion with patterns
mutual
  def even : Nat → Bool
    | 0 => true
    | n + 1 => odd n

  def odd : Nat → Bool
    | 0 => false
    | n + 1 => even n
end

-- Pattern matching with side conditions
def safeDivide : Nat → (m : Nat) → m ≠ 0 → Nat
  | n, 0, h => absurd rfl h
  | n, m + 1, _ => n / (m + 1)

-- Overlapping patterns with disambiguation
def f : Nat × Nat → Nat
  | (0, 0) => 0      -- Most specific
  | (0, _) => 1      -- Less specific
  | (_, 0) => 2      -- Less specific
  | (_, _) => 3      -- Least specific