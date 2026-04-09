import Mathlib.Tactic

/-!

This file defines a type SET.{ℓ} (which depends upon a universe variable ℓ)
that models ZFC plus "there exist ℓ strongly inaccesible cardinals".

It also provides a proof that the axioms of ZFC hold in this model.

## Implementation notes

The way SET is constructed is essentially as suggested by Werner in
*Sets in types, type in sets* (1997).

-/


infixr:55 "and"   => And
def patch {X : Type*} (f : ℕ → X) (z : ℕ) (x : X) : ℕ → X :=
  λt ↦ ite (t=z) x (f t)
universe ℓ

/-- This is the type of sets à la Werner (our type SET will actually be
a quotient of this by an equivalence relation) --/
inductive S : Type (ℓ+1) where
| sup : (∀ A : Type ℓ, (A → S) → S)

/-- Two sets p,q are equivalent iff they have the same elements.--/
def EXT (p q : S) : Prop :=
  match p with
  | S.sup A f =>
    match q with
    | S.sup B g =>
       (∀a:A, ∃b:B, EXT (f a) (g b)) ∧
       (∀b:B, ∃a:A, EXT (f a) (g b))

/-- p∈q iff p is equivalent to an element of q --/
def In (p q : S) : Prop :=
  match q with
  | S.sup A f =>
    ∃a:A, EXT p (f a)

/-- An empty type of sort ℓ --/
inductive Z : Type ℓ
/-- A type of sort ℓ with exactly two inhabitants --/
inductive Two : Type ℓ where
| a : Two
| b : Two

theorem ZtF (z : Z) : ⊥ := by
  have zr := @Z.rec
  set f : Z→Prop :=λ _↦⊥ with fdef
  have h := zr f z
  rwa[fdef] at h

/-- The empty set. --/
def SZ : S := S.sup Z (False.elim ∘ ZtF)

/-- The pairing map x,y↦{x,y} --/
def Pair : S → S → S :=
  λ(A B : S) ↦ S.sup Two (λ x ↦ match x with
                                 |Two.a => A
                                 |Two.b => B )

/-- The comprehension map that, given a set p and a map Q from S to Prop,
returns the subset of p whose elements satisfy Q. --/
def Compr (p : S)(Q : S → Prop) : S :=
  match p with
  | S.sup A f =>
    S.sup {val : A // Q (f val)}
          (λ a ↦ f a)

/-- The powerset of a set p is a set whose elements are the subsets of p --/
def Power (p : S) : S :=
  match p with
  | S.sup A f =>
    S.sup (A → Prop)
          (λ Q ↦
            S.sup {val : A // Q val}
                  (λ a ↦ f a))

def Base (p : S) : Type ℓ :=
  match p with
  | S.sup A _ => A
def Fun : (x: S) → (Base x) → S :=
  λ x ↦ match x with
        | S.sup _ f => f

/-- The union of a set p is a set whose elements are the elements of an element of p --/
def Un (p : S) : S :=
  match p with
  | S.sup A f =>
    S.sup (Σ a:A, Base (f a))
          (λ⟨a,fa⟩ ↦ (Fun (f a)) fa)

/-- The intersection of a set p is a set whose elements are the common elements of all elements of p.
(The intersection of two sets in the usual sense can be obtained by compounding this with Pair.) --/
def Inters (p : S) : S :=
  Compr (Un p) (λq ↦ ∀s:(Base p), (In q (Fun p s)))

/-- There exists an empty set. --/
theorem NullSet : ∃x:S, ¬∃y, In y x := by
  use SZ; by_contra a
  rcases a with ⟨z, hz⟩
  rw[SZ, In] at hz; dsimp at hz
  rcases hz with ⟨o, _⟩
  exact ZtF o

theorem EXTRefl (a : S) : EXT a a := by
  match a with
  | S.sup A f =>
    rw[EXT]; constructor
    <;> intro a <;> use a
    <;> exact EXTRefl (f a)
theorem EXTSymm (x y : S) : (EXT x y) → EXT y x := by
  match x with
  | S.sup A f =>
    match y with
    | S.sup B g =>
      intro E
      rw[EXT] at *;
      constructor
      . have := E.right
        intro b; have := this b
        rcases this with ⟨a, this⟩
        use a; apply EXTSymm (f a) (g b);
        exact this
      . have := E.left
        intro a; have := this a
        rcases this with ⟨b, this⟩
        use b; apply EXTSymm (f a) (g b);
        exact this
theorem EXTTrans (x y z : S) (h1: EXT x y) (h2: EXT y z) : EXT x z := by
  match x with
  | S.sup A f =>
    match y with
    | S.sup B g =>
      match z with
      | S.sup C h =>
        rw[EXT] at *;
        constructor
        . intro a
          have h1 := h1.left a
          rcases h1 with ⟨b, h1⟩
          have h2 := h2.left b
          rcases h2 with ⟨c, h2⟩
          use c; exact EXTTrans (f a) (g b) (h c) h1 h2
        . intro c
          have h2 := h2.right c
          rcases h2 with ⟨b, h2⟩
          have h1 := h1.right b
          rcases h1 with ⟨a, h1⟩
          use a; exact EXTTrans (f a) (g b) (h c) h1 h2
/-- The relation of equivalence between sets is indeed an equivalence relation. --/
theorem EXTEquiv : Equivalence EXT := by
  constructor
  exact EXTRefl
  intro x y; exact EXTSymm x y
  intro x y z; exact EXTTrans x y z

instance Sq : Setoid S where
  r := EXT
  iseqv := EXTEquiv

/-- We use as the type of sets the quotient of S by the equivalence relation that collapses
sets with the same elemets, so that sets that should be equal are indeed equal. --/
def SET := Quotient Sq

theorem InQ1 (x xx y yy : S) (hx: EXT x xx) (hy: EXT y yy) : (In x y) → (In xx yy) := by
  match x with
  | S.sup A f =>
    match y with
    | S.sup B g =>
      match xx with
      | S.sup AA ff =>
        match yy with
        | S.sup BB gg =>
          rw[EXT] at *;
          rw[In];
          rintro ⟨b, hb⟩
          have : EXT (S.sup AA ff) (S.sup A f) := by
            apply EXTSymm; exact hx
          have : EXT (S.sup AA ff) (g b) :=
            EXTTrans _ _ _ this hb
          have hyb := hy.left b
          rcases hyb with ⟨bb, hyb⟩
          have : EXT (S.sup AA ff) (gg bb) :=
            EXTTrans _ _ _ this hyb
          rw[In];  use bb
theorem InQ (x y xx yy : S) (hx: x ≈ xx) (hy: y ≈ yy) : (In x y) = (In xx yy) := by
  apply propext
  constructor
  . exact InQ1 _ _ _ _ hx hy
  . exact InQ1 _ _ _ _ (EXTSymm _ _ hx) (EXTSymm _ _ hy)

/-- The membership relation between sets in SET. --/
def IN (x y : SET.{ℓ}) :  Prop :=
  Quotient.lift₂ In InQ x y

/-- The empty set. --/
def NULL.{u} : SET.{u} := ⟦SZ⟧

theorem S_decomp : ∀s:S, s=S.sup (Base s) (Fun s) := by
  intro s
  match s with
  | S.sup A f => rfl

theorem UnQ (x y : S) (h: x ≈ y) : Un x ≈ Un y := by
  match x with
  | S.sup A f =>
    match y with
    | S.sup B g =>
      change EXT _ _ at *
      rw[EXT] at h;
      rw[Un,Un]; dsimp; rw[EXT];
      constructor
      . rintro ⟨a,fa⟩
        have h' := h.1 a
        rcases h' with ⟨b, h'⟩
        rw[S_decomp (f a), S_decomp (g b)] at h'
        rw[EXT] at h';
        have h' := h'.1 fa
        rcases h' with ⟨gb, h'⟩
        use ⟨b, gb⟩
      . rintro ⟨b, gb⟩
        have h' := h.2 b
        rcases h' with ⟨a, h'⟩
        rw[S_decomp (g b), S_decomp (f a)] at h'
        rw[EXT] at h';
        have h' := h'.2 gb
        rcases h' with ⟨fa, h'⟩
        use ⟨a, fa⟩
theorem UnQ'(x y : S) (h: x ≈ y) : Quotient.mk Sq (Un x) = Quotient.mk Sq (Un y) := by
  apply Quotient.eq.mpr; exact UnQ x y h

/-- The Union of a set in SET. --/
def UN : SET.{ℓ} → SET.{ℓ} :=
  λ x ↦ Quotient.lift (λ x ↦ Quotient.mk Sq (Un x)) UnQ' x

theorem PairQ (x y xx yy : S) (hx: x ≈ xx) (hy: y ≈ yy) : (Pair x y) ≈ (Pair xx yy) := by
  match x with
  | S.sup A f =>
    match y with
    | S.sup B g =>
      match xx with
      | S.sup AA ff =>
        match yy with
        | S.sup BB gg =>
          change EXT _ _ at *
          rw[Pair, Pair]; rw[EXT] at *
          constructor
          <;> intro t
              <;> match t with
                  | Two.a =>
                    use Two.a; dsimp
                    exact hx
                  | Two.b =>
                    use Two.b; dsimp
                    exact hy
theorem PairQ' (x y xx yy : S) (hx: x ≈ xx) (hy: y ≈ yy) : Quotient.mk Sq (Pair x y) = Quotient.mk Sq (Pair xx yy) := by
  apply Quotient.eq.mpr; exact PairQ x y xx yy hx hy

/-- The pair of two sets in SET. --/
def PAIR : SET.{ℓ} → SET.{ℓ} → SET.{ℓ} :=
  λ x y ↦ Quotient.lift₂ (λ x y ↦ Quotient.mk Sq (Pair x y)) PairQ' x y

theorem PowQ (x y : S) (h: x ≈ y) : (Power x) ≈ (Power y) := by
  change EXT _ _ at *
  match x with
  | S.sup A f =>
    match y with
    | S.sup B g =>
      rw[Power, Power]
      rw[EXT] at *;
      constructor
      . intro P
        have h' := h.1
        use λ b ↦ ∃a:A, (P a) ∧ (EXT (f a) (g b))
        set Q := λ b ↦ ∃a:A, (P a) ∧ (EXT (f a) (g b)) with Qdef
        rw[EXT];
        constructor
        . intro a
          rcases h' a with ⟨b, h''⟩
          have : Q b := by
            rw[Qdef]; beta_reduce; use a
            exact ⟨a.2, h''⟩
          use ⟨b, this⟩
        . rintro ⟨b, ⟨a, ⟨Pa, _⟩⟩⟩
          use ⟨a, Pa⟩
      . intro P
        have h' := h.2
        use λ a ↦ ∃b:B, (P b) ∧ (EXT (f a) (g b))
        set Q := λ a ↦ ∃b:B, (P b) ∧ (EXT (f a) (g b)) with Qdef
        rw[EXT];
        constructor
        . rintro ⟨a, ⟨b, ⟨Pb, _⟩⟩⟩
          use ⟨b, Pb⟩
        . intro b
          rcases h' b with ⟨a, h''⟩
          have : Q a := by
            rw[Qdef]; beta_reduce; use b
            exact ⟨b.2, h''⟩
          use ⟨a, this⟩
theorem PowQ' (x y : S) (h: x ≈ y) : Quotient.mk Sq (Power x) = Quotient.mk Sq (Power y) := by
  apply Quotient.sound; exact PowQ x y h

/-- The powerset of a set in SET. --/
def POW : SET.{ℓ} → SET.{ℓ} :=
  λ x ↦ Quotient.lift (λ x ↦ Quotient.mk Sq (Power x)) PowQ' x

noncomputable def pick_representation (x : SET.{ℓ}) : {s : S // ⟦s⟧=x} := by
  have : Nonempty {s : S // ⟦s⟧=x} := by
    apply nonempty_subtype.mpr
    exact Quot.exists_rep x
  exact Classical.choice this
theorem downpick (x : SET.{ℓ}) : ⟦↑(pick_representation x)⟧=x := by
  exact (pick_representation x).2

/-- **Axiom of Extensionality**: two sets are equal iff they have the same elements. --/
theorem EXTENSIONALITY : ∀(x y : SET.{ℓ}), (∀z:SET.{ℓ}, IN z x ↔ IN z y) → x=y := by
  intro x y hz
  set X := pick_representation x with Xdef
  set Y := pick_representation y with Ydef
  have : (∀Z:S, In Z X ↔ In Z Y) → EXT X Y := by
    simp only[S_decomp ↑X, S_decomp ↑Y, In, EXT]
    set A := Base X; set f := Fun X
    set B := Base Y; set g := Fun Y
    intro hZ
    constructor
    . intro a
      apply (hZ (f a)).mp
      use a; exact EXTRefl (f a)
    . intro b
      have : ∃a, EXT (g b) (f a) := by
        apply (hZ (g b)).mpr
        use b; exact EXTRefl (g b)
      rcases this with ⟨a, this⟩; use a
      exact EXTSymm _ _ this
  have zlift: ∀Z:S, In Z X ↔ In Z Y := by
    intro Z;
    show IN ⟦Z⟧ ⟦(X : S)⟧ ↔ IN ⟦Z⟧ ⟦Y⟧
    rw[Xdef, Ydef, downpick, downpick]
    exact hz ⟦Z⟧
  have : (X : S) ≈ Y := this zlift
  rw[← downpick x, ← downpick y, ← Xdef, ← Ydef]
  apply Quotient.sound; exact this

/-- **Axiom of pairing**: for any two sets x and y, there is a set whose elements are exactly x and y. --/
theorem PAIRING : ∀(x y : SET.{ℓ}),∃z:SET.{ℓ}, (IN x z)∧(IN y z) := by
  intro x y
  use PAIR x y
  set X := pick_representation x with Xdef
  set Y := pick_representation y with Ydef
  constructor
  . have : In (X : S) (Pair X Y) := by
      simp only[In, Pair]; use Two.a; beta_reduce; dsimp
      exact EXTRefl _
    rw[← downpick x, ← downpick y, ← Xdef, ← Ydef]
    exact this
  . have : In (Y : S) (Pair X Y) := by
      simp only[In, Pair]; use Two.b; beta_reduce; dsimp
      exact EXTRefl _
    rw[← downpick x, ← downpick y, ← Xdef, ← Ydef]
    exact this

/-- **Axiom of union**: every set has a union. --/
theorem UNION : ∀w:SET.{ℓ}, ∃u:SET.{ℓ}, ∀(x y : SET.{ℓ}), ((IN x y)∧(IN y w))→(IN x u) := by
  intro w; use UN w; intro x y
  set X := pick_representation x with Xdef
  set Y := pick_representation y with Ydef
  set W := pick_representation w with Wdef
  rw[← downpick x, ← downpick y, ← downpick w, ← Xdef, ← Ydef, ← Wdef]
  show ((In X Y) ∧ (In Y W)) → (In X (Un W))
  set X := (X : S); set Y := (Y : S); set W := (W : S)
  rintro ⟨hxy, hyw⟩
  simp only[Un]; simp only[In] at *
  rw[S_decomp X, S_decomp Y, S_decomp W] at *
  change ∃a, EXT (S.sup (Base X) (Fun X)) ((Fun Y) a) at hxy
  change ∃b, EXT (S.sup (Base Y) (Fun Y)) ((Fun W) b) at hyw
  rcases hxy with ⟨b, hxy⟩
  rcases hyw with ⟨c, hyw⟩
  rw[S_decomp (Fun W c), EXT] at hyw
  have hyw' := hyw.1 b
  rcases hyw' with ⟨b', hyw''⟩
  use ⟨c, b'⟩
  beta_reduce
  show EXT _ (Fun (Fun W c) b')
  exact EXTTrans _ _ _ hxy hyw''

/-- **Axiom of the powerset**: every set has a powerset. --/
theorem POWER : ∀x:SET.{ℓ},∃y:SET.{ℓ},∀z:SET.{ℓ}, (∀w:SET.{ℓ},(IN w z)→(IN w x))→(IN z y) := by
  intro x; use POW x; intro z
  set X := pick_representation x with Xdef
  set Z := pick_representation z with Zdef
  rw[← downpick x, ← downpick z, ← Xdef, ← Zdef]
  have : ∀(X Z:S), (∀W:S, In W Z → In W X) → In Z (Power X) := by
    intro X Z hsub
    match X with
    | S.sup A f =>
      match Z with
      | S.sup B g =>
        rw[Power,In];
        use λ a ↦ ∃b, EXT (g b) (f a)
        rw[EXT]; dsimp
        constructor
        . intro b
          have hsub := hsub (g b)
          have : In (g b) (S.sup B g) := by
            rw[In];  use b; exact EXTRefl _
          have hsub' := hsub this
          rw[In] at hsub';
          rcases hsub' with ⟨a, ha⟩
          have : ∃b, EXT (g b) (f a) := by use b
          set aa : { v // ∃ b, EXT (g b) (f v) } := ⟨a, this⟩
          use aa
        . intro a
          exact a.2
  have := this X Z
  intro hsub
  have is_sub : ∀ (W : S), In W (Z:S) → In W (X:S) := by
    intro W; have hsub := hsub ⟦W⟧
    intro hwz; exact hsub hwz
  exact this is_sub

theorem Two_Un (q X Y: S) : (In q (Un (Pair X Y))) ↔ ((In q X) ∨ (In q Y)) := by
  constructor <;> intro h
  . rw[Pair, Un] at h; dsimp at h
    rw[In] at h;
    rcases h with ⟨⟨two,e⟩ , h⟩
    match two with
    | Two.a =>
      dsimp at *; left
      rw[S_decomp X, In]; use e
    | Two.b =>
      dsimp at *; right
      rw[S_decomp Y, In]; use e
  . rcases h with h|h
    <;> rw[S_decomp X, S_decomp Y] at *
    <;> rw[In] at *;
    rcases h with ⟨a, h⟩
    rw[Pair, Un]; dsimp
    use ⟨Two.a, a⟩; dsimp; exact h
    rcases h with ⟨a, h⟩
    use ⟨Two.b, a⟩; dsimp; exact h

def S_succ (x : S) : S :=
  Un (Pair x (Pair x x))
inductive ℕℓ : Type ℓ where
| up: ℕ → ℕℓ
def nat (m : ℕ) : S :=
  match m with
  | 0   => SZ
  | m+1 => S_succ (nat m)
def upnat (m : ℕℓ) : S :=
  match m with
  | ℕℓ.up m => nat m

theorem SuccQ (x y : S) (h: x ≈ y) : (S_succ x) ≈ (S_succ y) := by
  rw[S_succ,S_succ]
  apply UnQ; apply PairQ; assumption
  apply PairQ <;> assumption

theorem SuccQ' (x y : S) (h: x ≈ y) : Quotient.mk Sq (S_succ x) = Quotient.mk Sq (S_succ y) := by
  apply Quotient.sound; exact SuccQ x y h

/-- The successor function x ↦ x∪{x}-/
def SUCC (x : SET.{ℓ}) : SET.{ℓ} :=
  Quotient.lift (λ x ↦ Quotient.mk Sq (S_succ x)) SuccQ' x

theorem PropSucc (x y : SET.{ℓ}) : (IN y (SUCC x)) ↔ ((IN y x) ∨ (y=x)) := by
  have : ∀(X Y : S), (In Y (S_succ X)) ↔ ((In Y X) ∨ (Y ≈ X)) := by
    intro X Y
    match X with
    | S.sup A f =>
      constructor <;> intro H
      . rw[S_succ] at H
        have H := (Two_Un _ _ _).mp H
        rcases H with H|H
        . left; exact H
        . right; rw[Pair,In] at H
          rcases H with ⟨t, H⟩
          match t with
          | Two.a => exact H
          | Two.b => exact H
      . apply (Two_Un _ _ _).mpr
        rcases H with H|H
        . left; exact H
        . right; rw[Pair,In]
          use Two.a; exact H
  set X := pick_representation x with Xdef
  set Y := pick_representation y with Ydef
  rw[← downpick x, ← downpick y, ← Xdef, ← Ydef]
  have := this X Y
  have j : ((Y:S)≈(X:S)) ↔ (Quotient.mk Sq (Y:S))=(Quotient.mk Sq (X:S)) := by
    exact Iff.symm Quotient.eq
  rw[j] at this; exact this

/-- **Axiom of infinity**: there exists a nonenmpty set closed by the successor.
(i.e., there exists an infinite set.) --/
theorem INFINITY : ∃N:SET.{ℓ}, (∃e:SET.{ℓ}, (∀z:SET.{ℓ}, ¬(IN z e))∧(IN e N)) ∧
                       (∀n:SET.{ℓ}, ∃sn:SET.{ℓ}, ((IN n N) → (IN sn N))
                                         ∧ (∀w, (IN w sn) ↔ ((IN w n) ∨ (w=n)))) := by
  use ⟦S.sup ℕℓ upnat⟧
  constructor
  . use NULL; constructor
    . intro z; by_contra raa
      set Z := pick_representation z with Zdef
      rw[← downpick z, ← Zdef, NULL] at raa
      change In Z SZ at raa
      simp only[In, SZ] at raa
      rcases raa with ⟨s,_⟩
      exact ZtF s
    . show In SZ (S.sup ℕℓ upnat)
      rw[In]; use ℕℓ.up 0
      exact EXTRefl _
  . intro m; use  SUCC m
    set M := pick_representation m with Mdef
    rw[← downpick m, ← Mdef]
    constructor
    . show In M (S.sup ℕℓ upnat) → In (S_succ M) (S.sup ℕℓ upnat)
      intro hm; rw[In] at *;
      rcases hm with ⟨k, hm⟩; set k' := k.1;
      use ℕℓ.up (k'+1)
      have : upnat (ℕℓ.up (k'+1)) = S_succ (upnat k) := by
        rw[upnat,upnat]; rw[nat]
      rw[this]
      have : EXT (S_succ (upnat k)) (S_succ M) := by
        apply EXTSymm _ _
        exact SuccQ M (upnat k) hm
      apply EXTSymm _ _
      exact this
    . apply PropSucc

  theorem Wf (x : S) : ∀(F:ℕ → S), (In (F 0) x) → ∃n:ℕ, ¬((In (F (n+1)) (F n))) := by
  by_contra raa
  have raa := not_forall.mp raa
  rcases raa with ⟨F, raa⟩
  rw[Classical.not_imp] at raa
  match x with
  | S.sup A f =>
    have F0 := raa.1
    have raa := raa.2
    have raa := not_exists.mp raa;
    have recur := λ a:A ↦ Wf (f a)
    rw[In] at F0;
    rcases F0 with ⟨a, F0⟩
    set G := λ n ↦ F (n+1)
    have recur := recur a G
    have : In (G 0) (f a) := by
      show In (F 1) (f a)
      have := raa 0
      rw[Classical.not_imp] at this
      have := this.1
      change In (F 1) (F 0) at this
      exact InQ1 (F 1) (F 1) (F 0) (f a) (EXTRefl _) F0 this
    have := recur this
    rcases this with ⟨n, boom⟩
    change ¬(In (F (n+2)) (F (n+1))) at boom
    have raa := raa (n+1)
    exact raa boom

noncomputable def Descent (x : S) (nonempty: ∃z, In z x) (h: ∀y, (In y x) → (∃w, (In w y)∧(In w x))) (n:ℕ) : {v:S // In v x} := by
  match n with
  | 0   =>
    let this : Nonempty {v:S//In v x} := Set.Nonempty.coe_sort nonempty
    exact Classical.choice this
  | m+1 =>
    match x with
    | S.sup A f =>
      set prev := Descent (S.sup A f) nonempty h m
      let this := h prev.1 prev.2
      let NE : Nonempty {w:S//(In w prev)∧(In w (S.sup A f))} := by
        exact Set.Nonempty.coe_sort this
      set nEXT := Classical.choice NE
      exact ⟨nEXT.1, nEXT.2.2⟩

/-- **Axiom of foundation**: for any set x, if it isn't empty, there is some y∈x s.t. y∩x=Ø --/
theorem FOUNDATION : ∀x:SET.{ℓ}, ((∃a:SET.{ℓ}, (IN a x)) → (∃y:SET.{ℓ}, (IN y x) ∧ ¬∃z:SET.{ℓ}, (IN z y)∧(IN z x))) := by
  have : ∀X:S, ((∃A:S, (In A X)) → (∃Y:S, (In Y X) ∧ ¬∃Z:S, (In Z Y)∧(In Z X))) := by
    intro X nonempty
    match X with
    | S.sup B f =>
      by_contra raa
      have raa := not_exists.mp raa
      simp only[not_and_not_right] at raa
      set F := Descent (S.sup B f) nonempty raa with Fdef
      have := (Wf (S.sup B f)) (λ n ↦ ↑(F n))
      have F0 : In (F 0) (S.sup B f) := by
        set F0 : {v:S//In v (S.sup B f)} := F 0
        exact F0.2
      have := this F0
      rcases this with ⟨n, hn⟩
      have FF : In (F (n+1)) (F n) := by
        rw[Fdef, Descent]
        set Z := Descent (S.sup B f) nonempty raa n
        have NE : Nonempty {w:S//(In w Z)∧(In w (S.sup B f))} := by
          exact Set.Nonempty.coe_sort (raa Z Z.2)
        show In ↑(Classical.choice NE) Z
        exact (Classical.choice NE).2.1
      exact hn FF
  intro x nem
  rcases nem with ⟨a, nem⟩
  set A := pick_representation a with Adef
  set X := pick_representation x with Xdef
  rw[← downpick a, ← downpick x, ← Adef, ← Xdef] at nem
  change In A X at nem
  have eAX : ∃A, In A X := Exists.intro (A:S) nem
  have := this X eAX
  rcases this with ⟨Y, emin⟩
  use ⟦Y⟧; constructor
  . rw[← downpick x, ← Xdef]
    exact emin.1
  . apply not_exists.mpr; intro z
    set Z := pick_representation z with Zdef
    rw[← downpick z, ← downpick x, ← Zdef, ← Xdef]
    show ¬((In Z Y) ∧ (In Z X))
    exact not_exists.mp emin.2 Z

/-- **Axiom of the empty set**: there exists an empty set. --/
theorem NULLSET : ∃z:SET.{ℓ},∀x:SET.{ℓ}, ¬(IN x z) := by
  use ⟦SZ⟧; intro x
  set X := pick_representation x with Xdef
  rw[← downpick x, ← Xdef]
  show ¬(In X SZ)
  rw[S_decomp X, S_decomp SZ]
  rw[In]; by_contra raa
  rcases raa with ⟨a, _⟩
  exact ZtF a

def downsub (X:S) (x:SET.{ℓ}) (h: ⟦X⟧=x) (Y:{V:S//In V X}) : {v:SET.{ℓ}//IN v x} := by
  have : ∀Y,((In Y X) → (IN ⟦Y⟧ x)) := by
    intro Y; rw[← h]
    intro I; exact I
  exact ⟨Quotient.mk Sq Y.1,  (this Y.1) Y.2⟩
theorem downsubQ (X:S) (x:SET.{ℓ}) (h: ⟦X⟧=x) (Y:{V:S//In V X}) : ((downsub X x h Y) : SET.{ℓ}) = Quotient.mk Sq Y := by
  rw[downsub]

/-- **Axiom of replacement**: the image of a set along a definable class function is a set. --/
theorem REPLACEMENT' : ∀x:SET.{ℓ}, ∀f:{v:SET.{ℓ}//IN v x}→SET.{ℓ}, ∃y:SET.{ℓ}, ∀z:SET.{ℓ}, (IN z y) ↔ (∃w, (f w)=z) := by
  intro x f
  set X := pick_representation x with Xdef
  have h : Quotient.mk Sq X=x := by
    rw[Xdef]; exact downpick (x : SET.{ℓ})
  set F:{V:S//In V X}→S := λV ↦ pick_representation (f (downsub X x h V)) with Fdef
  have : ∃ Y, ∀ (Z : S), In Z Y ↔ ∃ W, EXT (F W) Z := by
    set A := Base X
    set g := Fun X with gdef
    have : ∀a:A, In (g a) X := by
      intro a; rw[S_decomp X, In];
      use a; apply EXTRefl
    set Fa:A→S := λ a ↦ F ⟨g a, this a⟩
    use S.sup A Fa
    intro Z; constructor <;> intro H
    . rw[In] at H
      rcases H with ⟨a, H⟩
      use ⟨g a, this a⟩
      exact EXTSymm _ _ H
    . rcases H with ⟨W, H⟩
      have W2 := W.2
      simp only[S_decomp X] at W2
      rw[In] at W2
      rcases W2 with ⟨a, W2⟩
      change EXT W (g a) at W2
      rw[In]; use a
      have FEXT : (F W) ≈ (F ⟨g a, this a⟩) := by
        apply Quotient.eq.mp
        rw[Fdef]; dsimp
        rw[downpick _, downpick _]
        rw[downsub, downsub]; dsimp
        apply congr_arg
        have : Quotient.mk Sq W = Quotient.mk Sq (Fun (↑(pick_representation x)) a) := by
          apply Quotient.sound
          rw[← gdef]; exact W2
        simp only[this]
        exact rfl
      exact EXTTrans _ _ _ (EXTSymm _ _ H) FEXT
  rcases this with ⟨Y, this⟩; use ⟦Y⟧
  intro z
  set Z := pick_representation z with Zdef
  rw[← downpick z, ← Zdef]; constructor <;> intro H
  . rcases (this Z).mp H with ⟨W, H⟩
    use downsub _ _ h W
    rw[← downpick (f (downsub (↑X) x h W))]
    apply Quotient.sound; exact H
  . rcases H with ⟨w, H⟩
    set W := pick_representation w with Wdef
    have WX : In W X := by
      have := w.2
      simp only[← downpick w, ← Wdef, ← h] at this
      exact this
    have FWZ : (F ⟨W, WX⟩ ) ≈ Z := by
      apply Quotient.eq.mp
      dsimp; rw[Fdef]; beta_reduce; rw[downsub]; dsimp
      simp only[Zdef]; rw[downpick, ←Zdef]
      simp only[Wdef, downpick]
      exact H
    set W : {V:S//In V X} := { val := ↑W, property := WX }
    exact (this Z).mpr (Exists.intro W FWZ)

/-- **Axiom of comprehension**: the intersection of a set with a definable class is a set. --/
theorem COMPREHENSION' : ∀x:SET.{ℓ}, ∀f:SET.{ℓ}→Prop, ∃y:SET.{ℓ}, ∀z:SET.{ℓ}, (IN z y) ↔ ((IN z x) ∧ (f z)) := by
  have : ∀X:S, ∀F:S→Prop, ∀_:(∀(U V:S),((U≈V) → ((F U)=(F V)))), ∃Y:S, ∀Z:S, (In Z Y) ↔ ((In Z X) ∧ (F Z)) := by
    intro X F Fgood; use Compr X F; intro Z
    match X with
    | S.sup A g =>
      constructor <;> intro H
      . rw[Compr, In] at H;
        rcases H with ⟨a, h⟩
        constructor
        . rw[In]; use a
        . have := Fgood Z (g a) h
          rw[this]; exact a.2
      . rw[Compr, In];
        rw[In] at H;
        rcases H.1 with ⟨a, H1⟩
        have H2 := H.2
        have := Fgood Z (g a) H1
        rw[this] at H2
        use ⟨a, H2⟩
  intro x f
  set F:S → Prop := λ U ↦ f ⟦U⟧ with Fdef
  set X := pick_representation x with Xdef
  have Fgood : ∀(U V:S),((U≈V) → ((F U)=(F V))) := by
    intro U V eUV
    have eUV := Quotient.sound eUV
    rw[Fdef]; beta_reduce; rw[eUV]
  have := this X F Fgood
  rcases this with ⟨Y, this⟩; use ⟦Y⟧
  intro z
  set Z := pick_representation z with Zdef
  rw[← downpick x, ← downpick z, ← Xdef, ← Zdef]
  exact this Z
