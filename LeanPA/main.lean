import LeanPA.sets
universe ℓ

/- Utility functions to write the translation φ ↦ (φ_Z)_M-/
def is_zero (x : SET.{ℓ}) : Prop := ∀z:SET.{ℓ}, ¬(IN z x)
def is_one (x : SET.{ℓ}) : Prop := ∀z:SET.{ℓ}, (IN z x)↔(is_zero z)
def is_sub (x y : SET.{ℓ}) : Prop := ∀z:SET.{ℓ}, (IN z x)→(IN z y)
def is_pair (x y z : SET.{ℓ}) : Prop := ∀a:SET.{ℓ}, (IN a z) ↔ ((a=x) ∨ (a=y))
def is_single (x y : SET.{ℓ}) : Prop := is_pair x x y
def is_couple (x y z : SET.{ℓ}) : Prop :=
  ∃a, ∃b, (is_pair a b z) ∧ (is_single x a) ∧ (is_pair x y b)
def is_power (x y : SET.{ℓ}) : Prop := ∀a, (is_sub a x) ↔ (IN a y)
def is_prod (x y z : SET.{ℓ}) : Prop :=
  ∀ab, (IN ab z) ↔ (∃a, ∃b, (IN a x) ∧ (IN b y) ∧ (is_couple a b ab))
def is_union (x y z : SET.{ℓ}) : Prop :=
  ∀a, (IN a z) ↔ (IN a x) ∨ (IN a y)
def is_disj_union (x y z : SET.{ℓ}) : Prop :=
  ∃x0, ∃y1, ∃v, ∃vv, ∃o, ∃oo, (is_union x0 y1 z)
                             ∧ (is_prod x vv x0)
                             ∧ (is_prod y oo y1)
                             ∧ (is_single v vv)
                             ∧ (is_single o oo)
                             ∧ (is_zero v)
                             ∧ (is_one o)


theorem pair_ok : ∀a, ∀b, ∃!ab, is_pair a b ab := by
  intro a b; apply existsUnique_of_exists_of_unique
  . have := PAIRING a b
    rcases this with ⟨ab, this⟩
    have comp := COMPREHENSION' ab (λc ↦ (c=a) ∨ (c=b))
    rcases comp with ⟨ab', comp⟩; use ab'
    rw[is_pair]; intro z; constructor <;> intro H
    . exact ((comp z).mp H).2
    . apply (comp z).mpr
      have zab : IN z ab := by
        rcases H with za|zb
        . have this := this.1; rwa[za]
        . have this := this.2; rwa[zb]
      exact ⟨zab, H⟩
  . intro ab ab' H H'
    apply (EXTENSIONALITY ab ab')
    intro z; rw[is_pair] at *
    constructor <;> intro zin
    . exact (H' z).mpr ((H z).mp zin)
    . exact (H z).mpr ((H' z).mp zin)

theorem single_ok : ∀a, ∃!aa, is_single a aa := by
  simp only[is_single]; intro a
  exact pair_ok a a

theorem couple_ok : ∀a, ∀b, ∃!ab, is_couple a b ab := by
  intro a b; simp only[is_couple]
  set a' := (single_ok a).exists.choose
  set ab' := (pair_ok a b).exists.choose
  set ab := (pair_ok a' ab').exists.choose
  apply existsUnique_of_exists_of_unique
  . use ab; use a'; use ab'
    exact ⟨(pair_ok a' ab').exists.choose_spec,
           ⟨(single_ok a).exists.choose_spec,
            (pair_ok a b).exists.choose_spec⟩⟩
  . intro ab1 ab2 H1 H2
    rcases H1 with ⟨p1, ⟨q1, ⟨H1, ⟨J1, K1⟩⟩⟩⟩
    rcases H2 with ⟨p2, ⟨q2, ⟨H2, ⟨J2, K2⟩⟩⟩⟩
    have K : q1=q2 := (pair_ok a b).unique K1 K2
    have J : p1=p2 := (single_ok a).unique J1 J2
    rw[K, J] at H1
    exact (pair_ok _ _).unique H1 H2

theorem power_ok : ∀a, ∃!Pa, is_power a Pa := by
  intro a; apply existsUnique_of_exists_of_unique
  . simp only[is_power, is_sub]
    have pow := POWER a
    rcases pow with ⟨P, pow⟩
    have comp := COMPREHENSION' P (λc ↦ (is_sub c a))
    rcases comp with ⟨P', comp⟩
    use P'; intro z; constructor <;> intro H
    . apply (comp z).mpr
      exact ⟨pow z H, H⟩
    . exact ((comp z).mp H).2
  . intro P P' H H'
    rw[is_power] at *
    apply EXTENSIONALITY _ _
    intro z; constructor <;> intro zin
    . exact (H' z).mp ((H z).mpr zin)
    . exact (H z).mp ((H' z).mpr zin)

theorem union_ok : ∀a, ∀b, ∃!ab, is_union a b ab := by
  intro a b; apply existsUnique_of_exists_of_unique
  . simp only[is_union]
    have p := pair_ok a b
    have hp := p.exists.choose_spec
    set ab := p.exists.choose
    rw[is_pair] at hp
    have un := UNION ab
    rcases un with ⟨U, un⟩
    have comp := COMPREHENSION' U (λc ↦ (IN c a)∨(IN c b))
    rcases comp with ⟨U', comp⟩
    use U'; intro z; constructor <;> intro H
    . exact ((comp z).mp H).2
    . rcases H with za|zb
      . have un := un z a
        have hp := (hp a).mpr (Or.inl rfl)
        have zu := un ⟨za, hp⟩
        exact (comp z).mpr ⟨zu, Or.inl za⟩
      . have un := un z b
        have hp := (hp b).mpr (Or.inr rfl)
        have zu := un ⟨zb, hp⟩
        exact (comp z).mpr ⟨zu, Or.inr zb⟩
  . intro U U' H H'
    rw[is_union] at *
    apply EXTENSIONALITY _ _
    intro z; constructor <;> intro zin
    . exact (H' z).mpr ((H z).mp zin)
    . exact (H z).mpr ((H' z).mp zin)

theorem prod_ok : ∀a, ∀b, ∃!ab, is_prod a b ab := by
  intro a b; apply existsUnique_of_exists_of_unique
  simp only[is_prod]
  have u := union_ok a b
  have hu := u.exists.choose_spec; set U := u.exists.choose
  have p1 := power_ok U
  have hp1 := p1.exists.choose_spec; set PU := p1.exists.choose
  have p2 := power_ok PU
  have hp2 := p2.exists.choose_spec; set PPU := p2.exists.choose
  have comp := COMPREHENSION' PPU (λc ↦ ∃x, ∃y, (IN x a) ∧ (IN y b) ∧ (is_couple x y c))
  rcases comp with ⟨X, comp⟩; use X
  intro z; constructor <;> intro H
  . exact ((comp z).mp H).2
  . apply (comp z).mpr; constructor
    . rcases H with ⟨x, ⟨y, ⟨H, ⟨J, K⟩⟩⟩⟩
      rw[is_power] at hp2
      apply (hp2 z).mp
      rw[is_sub]; intro w wz
      rw[is_power] at hp1
      apply (hp1 w).mp
      rw[is_sub]; intro t tw
      rw[is_couple] at K
      rcases K with ⟨xx, ⟨xy, ⟨H1, ⟨H2, H3⟩⟩⟩⟩
      rw [is_pair] at H1
      have H1! := (H1 w).mp wz
      rcases H1! with hxx | hxy
      . rw[is_single, ← hxx, is_pair] at H2
        have H2! := (H2 t).mp tw
        have H2! : t=x := by rcases H2! with h|h <;> exact h
        rw[← H2!] at H
        rw[is_union] at hu
        apply (hu t).mpr
        left; exact H
      . simp only[is_pair, ← hxy] at H3
        have H3! := (H3 t).mp tw
        rw[is_union] at hu
        apply (hu t).mpr
        rcases H3! with hx|hy
        . rw[← hx] at H; left; exact H
        . rw[← hy] at J; right; exact J
    . exact H
  . intro P P' H H'
    rw[is_prod] at *; apply EXTENSIONALITY _ _
    intro z; constructor <;> intro zin
    . exact (H' z).mpr ((H z).mp zin)
    . exact (H z).mpr ((H' z).mp zin)

theorem zero_ok : ∃!z, is_zero z := by
  apply existsUnique_of_exists_of_unique
  . simp only[is_zero]; exact NULLSET
  . intro Z Z' H H'
    rw[is_zero] at *; apply EXTENSIONALITY _ _
    intro z; constructor <;> intro zin <;> exfalso
    . exact (H z) zin
    . exact (H' z) zin
theorem one_ok : ∃!o, is_one o := by
  apply existsUnique_of_exists_of_unique
  . simp only[is_one]
    have hz := zero_ok; set z := hz.exists.choose
    have ho := single_ok z; set o := ho.exists.choose
    use o; intro a; constructor <;> intro H
    . have := ho.exists.choose_spec
      change is_single z o at this
      rw[is_single, is_pair] at this
      have := (this a).mp H
      have : a=z := by rcases this with h|h <;> exact h
      have j := hz.exists.choose_spec; change is_zero z at j
      rwa[this]
    . have ho := ho.exists.choose_spec; change is_single z o at ho
      rw[is_single, is_pair] at ho
      apply (ho a).mpr; left
      have hz := hz.exists.choose_spec; change is_zero z at hz
      exact zero_ok.unique H hz
  . intro O O' H H'
    rw[is_one] at *; apply EXTENSIONALITY _ _
    intro z; constructor <;> intro zin
    . exact (H' z).mpr ((H z).mp zin)
    . exact (H z).mpr ((H' z).mp zin)

theorem disj_union_ok : ∀a, ∀b, ∃!ab, is_disj_union a b ab := by
  intro a b; apply existsUnique_of_exists_of_unique
  . simp only[is_disj_union]
    have z := zero_ok; have hz := z.exists.choose_spec; set v := z.exists.choose
    have u := one_ok; have hu := u.exists.choose_spec; set o := u.exists.choose
    have pv := single_ok v; have hpv := pv.exists.choose_spec; set vv := pv.exists.choose
    have po := single_ok o; have hpo := po.exists.choose_spec; set oo := po.exists.choose
    have xA := prod_ok a vv; have hxA := xA.exists.choose_spec; set A := xA.exists.choose
    have xB := prod_ok b oo; have hxB := xB.exists.choose_spec; set B := xB.exists.choose
    have u := union_ok A B; have hu := u.exists.choose_spec; set U := u.exists.choose
    use U; use A; use B; use v; use vv; use o; use oo
  . intro U U' H H'
    rw[is_disj_union] at *; apply EXTENSIONALITY _ _
    intro z;
    rcases H with ⟨x0, ⟨y1, ⟨v, ⟨vv, ⟨o, ⟨oo, H⟩⟩⟩⟩⟩⟩
    rcases H' with ⟨x0', ⟨y1', ⟨v', ⟨vv', ⟨o', ⟨oo', H'⟩⟩⟩⟩⟩⟩
    have ev : v=v' := zero_ok.unique H.2.2.2.2.2.1 H'.2.2.2.2.2.1
    have eo : o=o' := one_ok.unique H.2.2.2.2.2.2 H'.2.2.2.2.2.2
    rw[← ev, ← eo] at H'
    have evv : vv=vv' := (single_ok v).unique H.2.2.2.1 H'.2.2.2.1
    have eoo : oo=oo' := (single_ok o).unique H.2.2.2.2.1 H'.2.2.2.2.1
    rw[← evv, ← eoo] at H'
    have ex : x0=x0' := (prod_ok _ _).unique H.2.1 H'.2.1
    have ey : y1=y1' := (prod_ok _ _).unique H.2.2.1 H'.2.2.1
    rw[← ex, ← ey] at H'
    have eU : U=U' := (union_ok _ _).unique H.1 H'.1
    rw[eU]

/-- Two sets x, y have the same cardinality iff there is a set which is a bijection from x to y. --/
def is_equicard (x y : SET.{ℓ}) : Prop :=
  ∃P, ∃f, (is_prod x y P) ∧ (is_sub f P) ∧
          (∀a, (IN a x) → (∃!b, (IN b y) ∧ (∃c, (is_couple a b c) ∧ (IN c f)))) ∧
          (∀b, (IN b y) → (∃!a, (IN a x) ∧ (∃c, (is_couple a b c) ∧ (IN c f))))

def is_succ' (x y : SET.{ℓ}) : Prop :=
  ∃xx, (is_union x xx y) ∧ (is_single x xx)

theorem succ'_ok (x : SET.{ℓ}) : ∃!y, is_succ' x y := by
  simp only[is_succ']; apply existsUnique_of_exists_of_unique
  . have px := single_ok x; have hpx := px.exists.choose_spec; set xx := px.exists.choose
    have u := union_ok x xx; have hu := u.exists.choose_spec; set S := u.exists.choose
    use S; use xx
  . intro S S' H H'
    rcases H with ⟨xx, H⟩
    rcases H' with ⟨xx', H'⟩
    have : xx=xx' := (single_ok _).unique H.2 H'.2
    rw[← this] at H'
    exact (union_ok _ _).unique H.1 H'.1

def is_succ (x y : SET.{ℓ}) : Prop := ∀a, (IN a y) ↔ ((IN a x) ∨ (a = x))

theorem succ_ok (x : SET.{ℓ}) : ∃!y, is_succ x y := by
  simp only[is_succ]; apply existsUnique_of_exists_of_unique
  . have s := succ'_ok x; have hs := s.exists.choose_spec; set S := s.exists.choose
    rw[is_succ'] at hs; rcases hs with ⟨xx, ⟨J, K⟩⟩
    use S; intro a; constructor <;> intro H
    . rw[is_union] at J; have J := (J a).mp H
      rcases J with J|J
      . left; assumption
      . right; rw[is_single, is_pair] at K
        have K := (K a).mp J
        rcases K with K|K <;> exact K
    . rcases H with H|H
      . rw[is_union] at J; exact (J a).mpr (Or.inl H)
      . rw[is_union] at J; apply (J a).mpr; right
        rw[is_single, is_pair] at K
        exact (K a).mpr (Or.inl H)
  . intro S S' H H'
    apply EXTENSIONALITY _ _
    intro z; constructor <;> intro zin
    . exact (H' z).mpr ((H z).mp zin)
    . exact (H z).mpr ((H' z).mp zin)

theorem couple_works (a a' b b' c : SET.{ℓ}): (is_couple a a' c) → (is_couple b b' c) → (a=b) ∧ (a'=b') := by
  intro ha hb
  have hab : a=b := by
    rw[is_couple] at *
    rcases ha with ⟨A, ⟨AA, ⟨cA, ⟨sA,  _⟩⟩⟩⟩
    rcases hb with ⟨B, ⟨BB, ⟨cB, ⟨sB, pB⟩⟩⟩⟩
    rw[is_single, is_pair] at *
    have := (cB A).mp ((cA A).mpr (Or.inl rfl))
    rcases this with H|H
    . have : IN a A := (sA a).mpr (Or.inl rfl); rw[H] at this
      rcases (sB a).mp this with h|h <;> assumption
    . have : IN b BB := (pB b).mpr (Or.inl rfl); rw[← H] at this
      rcases (sA b).mp this with h|h <;> symm <;> assumption
  constructor
  . exact hab
  . rw[hab] at ha
    rw[is_couple] at *
    rcases ha with ⟨A, ⟨AA, ⟨cA, ⟨sA, pA⟩⟩⟩⟩
    rcases hb with ⟨B, ⟨BB, ⟨cB, ⟨sB, pB⟩⟩⟩⟩
    rw[is_single, is_pair] at *
    rcases (cB AA).mp ((cA AA).mpr (Or.inr rfl)) with h|h
    . have := (pA a').mpr (Or.inr rfl); rw[h] at this
      have : a'=b := by rcases (sB a').mp this with j|j <;> assumption
      simp only[this] at *
      rcases (cA BB).mp ((cB BB).mpr (Or.inr rfl)) with j|j
      . have := (pB b').mpr (Or.inr rfl); rw[j] at this
        rcases (sA b').mp this with h|h <;> symm <;> assumption
      . have := (pB b').mpr (Or.inr rfl); rw[j] at this
        rcases (pA b').mp this with h|h <;> symm <;> assumption
    . have := (pB b').mpr (Or.inr rfl); rw[← h] at this
      rcases (pA b').mp this with j|j
      . simp only[j] at *
        have := (pA a').mpr (Or.inr rfl); rw[h] at this
        rcases (pB a').mp this with j|j <;> assumption
      . symm; assumption

/-- A set is inductive if it contains the empty set and is closed for successor. --/
def is_inductive (N : SET.{ℓ}) : Prop :=
  (∃e, (is_zero e) ∧ (IN e N)) ∧
  (∀n, ∃s, ((IN n N) → (IN s N)) ∧ (is_succ n s))
/-- The set ω is the intersection of all indictive sets. --/
def is_omega (ω : SET.{ℓ}) : Prop :=
  (is_inductive ω) ∧ (∀N, (is_inductive N) → (is_sub ω N))
/-- A set is "a natural" iff it is a member of ω. --/
def is_natural (n : SET.{ℓ}) : Prop :=
  ∃ω, (is_omega ω) ∧ (IN n ω)

/-- There is an inductive set. --/
theorem ind_ex : ∃N, is_inductive N := by
  simp only[is_inductive, is_zero, is_succ]
  exact INFINITY
theorem omega_ok : ∃!ω, is_omega ω := by
  have eN := ind_ex; have hN := eN.choose_spec; set N := eN.choose
  apply existsUnique_of_exists_of_unique
  . have comp := COMPREHENSION' N (λc ↦ ∀X, (is_inductive X) → (IN c X))
    rcases comp with ⟨ω, comp⟩; use ω
    simp only[is_omega, is_sub]; constructor
    . rw[is_inductive]; constructor
      . have z := zero_ok; have hz := z.exists.choose_spec; set v := z.exists.choose; use v
        constructor; assumption
        apply (comp v).mpr; constructor
        . rw[is_inductive] at hN; have hN := hN.1
          rcases hN with ⟨v', ⟨hN, J⟩⟩
          have : v=v' := zero_ok.unique hz hN
          rw[this]; exact J
        . intro X indX
          rw[is_inductive] at indX; have indX := indX.1
          rcases indX with ⟨v', ⟨indX, J⟩⟩
          have : v=v' := zero_ok.unique hz indX
          rw[this]; exact J
      . intro n
        have s := succ_ok n; have hs := s.exists.choose_spec; set S := s.exists.choose
        use S; constructor
        . intro H
          have ⟨j,comp'⟩ := (comp n).mp H
          apply (comp S).mpr; constructor
          . rw[is_inductive] at hN; have hN := hN.2 n
            rcases hN with ⟨S', ⟨J, hN⟩⟩
            have : S=S' := (succ_ok n).unique hs hN
            rw[this]; exact J j
          . intro X indX'; have indX := indX'
            rw[is_inductive] at indX; have indX := indX.2 n
            rcases indX with ⟨S', ⟨J, indX⟩⟩
            have : S=S' := (succ_ok n).unique hs indX
            rw[this]; apply J
            exact ((comp n).mp H).2 X indX'
        . exact hs
    . intro X indX z zw
      exact ((comp z).mp zw).2 X indX
  intro ω ω' H H'
  simp only[is_omega] at *
  apply EXTENSIONALITY _ _
  intro z; constructor <;> intro zin
  . have H := H.2 ω' H'.1; rw[is_sub] at H; exact H z zin
  . have H' := H'.2 ω H.1; rw[is_sub] at H'; exact H' z zin

/-- This is the relation that codes whether a set x is the finite Von Neumann ordinal which corresponds to the natural n --/
def is_number (n : ℕ) (x : SET.{ℓ}) : Prop :=
  match n with
  | 0 => is_zero x
  | n+1 => ∃y, (is_number n y) ∧ (is_succ y x)

theorem number_ok (n : ℕ) : ∃!x, (is_number n x) := by
  induction n with
  | zero => simp only[is_number]; exact zero_ok
  | succ n ip =>
    simp only [is_number]
    apply existsUnique_of_exists_of_unique
    . have hy := ip.exists.choose_spec; set y := ip.exists.choose
      have s := succ_ok y; have hs := s.exists.choose_spec; set S := s.exists.choose
      use S; use y
    . intro x x' H H'
      rcases H with ⟨y, H⟩
      rcases H' with ⟨y', H'⟩
      have : y=y' := ip.unique H.1 H'.1
      rw[← this] at H'
      exact (succ_ok _).unique H.2 H'.2

theorem number_is_natural (n : ℕ) : ∀x, (is_number n x) → (is_natural x) := by
  intro x H; rw[is_natural]
  match n with
  | 0 =>
    . rw[is_number] at H
      have := omega_ok.exists; use this.choose
      constructor; exact this.choose_spec
      have hw :=this.choose_spec; set ω := this.choose
      rw[is_omega] at hw; have hw := hw.1
      rw[is_inductive] at hw; have hw := hw.1
      rcases hw with ⟨x', ⟨H',J⟩⟩
      have : x=x' := zero_ok.unique H H'
      rw[this]; assumption
  | n+1 =>
    . rw[is_number] at H; rcases H with ⟨y, ⟨H,J⟩⟩
      have H := number_is_natural n y H
      rw[is_natural] at H
      have hw := H.choose_spec; set ω := H.choose
      use ω; constructor; exact hw.1
      rw[is_omega, is_inductive] at hw
      rcases hw.1.1.2 y with ⟨x', ⟨h, j⟩⟩
      have : x=x' := (succ_ok _).unique J j; rw[← this] at h
      exact h hw.2

theorem carve_omega (X : SET.{ℓ}) (H : is_inductive X) :
    ∃N, (is_sub N X) ∧ (is_inductive N) ∧
        (∀x, (IN x N) → (∃n, is_number n x)) := by
  have comp₀ := COMPREHENSION' X (λc ↦ (∃n, is_number n c))
  rcases comp₀ with ⟨N, comp⟩; use N
  constructor
  . rw[is_sub]; intro z zin; exact ((comp z).mp zin).1
  . constructor
    . rw[is_inductive]; constructor
      . rw[is_inductive] at H
        rcases H.1 with ⟨v, ⟨hv, j⟩⟩
        use v; constructor; exact hv
        apply (comp v).mpr
        constructor; exact j
        use 0; rw[is_number]; exact hv
      . intro n
        have s := succ_ok n; have hs := s.exists.choose_spec; set S := s.exists.choose
        use S; constructor
        . intro hn
          rcases ((comp n).mp hn).2 with ⟨m, hm⟩
          have Snum : is_number (m+1) S := by rw[is_number]; use n
          have SX : IN S X := by
            rw[is_inductive] at H
            have H := H.2 n; rcases H with ⟨S', ⟨J,H⟩⟩
            have : S=S' := (succ_ok _).unique hs H
            rw[← this] at J
            exact J ((comp n).mp hn).1
          apply (comp S).mpr
          constructor; exact SX; use m+1
        . exact hs
    . intro z zin
      exact ((comp z).mp zin).2

theorem natural_is_number (x : SET.{ℓ}) : (is_natural x) → (∃n, is_number n x) := by
  intro H
  rw[is_natural] at H
  rcases H with ⟨ω, ⟨hw, hx⟩⟩
  rw[is_omega] at hw
  have hind := hw.1; have hmin := hw.2
  have carve := carve_omega ω hind
  rcases carve with ⟨carving, carve⟩
  have hmin := hmin carving carve.2.1
  rw[is_sub] at hmin
  exact carve.2.2 x (hmin x hx)

/-- The type of ℕ and the subtype of SET of the elements of ω are in bijection. --/
theorem isoN : ∀x, (is_natural x) ↔ ∃n, (is_number n x) := by
  intro x; constructor
  . exact natural_is_number x
  . intro H; rcases H with ⟨n, H⟩
    exact number_is_natural n x H

def is_plus (x y z : SET.{ℓ}) : Prop :=
  ∃u, (is_disj_union x y u) ∧ (is_equicard u z) ∧ (is_natural z)
def is_mult (x y z : SET.{ℓ}) : Prop :=
  ∃p, (is_prod x y p) ∧ (is_equicard p z) ∧ (is_natural z)

theorem number_card (n : ℕ) : ∀ x, (is_number n x) → ∃f:SET.{ℓ}→ℕ, (∀m<n, ∃!a, (IN a x) ∧ (f a = m)) ∧
                                                                (∀a, (IN a x) → (f a < n))  := by
  intro x H
  match n with
  | 0 =>
    . rw[is_number, is_zero] at H
      use λ_↦0; constructor
      . intro a ha; exfalso; exact Nat.not_succ_le_zero a ha
      . intro z hz; exfalso; exact H z hz
  | n+1 =>
    . rw[is_number] at H; rcases H with ⟨y, H⟩
      have hg := number_card n y H.1
      rcases hg with ⟨g, hg⟩
      use λa ↦ @ite ℕ (a=y) (Classical.dec (a=y)) n (g a)
      constructor
      . intro m hm
        by_cases h: m<n
        . have _ := hg.1
          have hg := hg.1 m h
          rcases hg.exists with ⟨a, hge⟩
          apply existsUnique_of_exists_of_unique
          . use a; constructor
            . have H' := H.2; have h' := hge.1
              rw [is_succ] at H'
              exact (H' a).mpr (Or.inl h')
            . have : ¬(a=y) := by
                by_contra raa
                have h' := hge.1; rw[raa] at h'
                have sy := single_ok y; have hY := sy.exists.choose_spec; set Y := sy.exists.choose
                have nF : ∃a, IN a Y := by use y; rw[is_single, is_pair] at hY; exact (hY y).mpr (Or.inl rfl)
                have F := FOUNDATION Y nF
                rcases F with ⟨y', ⟨hy', F⟩⟩
                absurd F; use y'
                have : y'=y := by
                  rw[is_single, is_pair] at hY
                  rcases (hY y').mp hy' with h|h <;> exact h
                rw[← this] at h'
                exact ⟨h', hy'⟩
              simp only[this]; dsimp; exact hge.2
          . intro q q' K K'
            have nqy : ¬(q=y) := by
              by_contra raa
              simp only[raa] at K; dsimp at K
              absurd K.2; exact Nat.ne_of_gt h
            have nqy' : ¬(q'=y) := by
              by_contra raa
              simp only[raa] at K'; dsimp at K'
              absurd K'.2; exact Nat.ne_of_gt h
            simp only[nqy, nqy'] at K K'; dsimp at K K'
            have J := K.2; have J' := K'.2
            have iqy : IN q y := by
              have H := H.2
              rw[is_succ] at H
              have H := (H q).mp K.1
              rcases H with H|H; assumption; absurd nqy H; trivial
            have iqy' : IN q' y := by
              have H := H.2
              rw[is_succ] at H
              have H := (H q').mp K'.1
              rcases H with H|H; assumption; absurd nqy' H; trivial
            exact hg.unique ⟨iqy, J⟩ ⟨iqy', J'⟩
        . have h : m=n := by exact Nat.eq_of_lt_succ_of_not_lt hm h
          apply existsUnique_of_exists_of_unique
          . use y; constructor
            . have H := H.2; rw[is_succ] at H
              exact (H y).mpr (Or.inr rfl)
            . simp only[]; dsimp; symm; assumption
          . intro q q' K K'
            rw[h] at K K'
            have eqy : q=y := by
              by_contra raa; simp only[raa] at K; dsimp at K
              have : IN q y := by
                have H := H.2; have K := K.1
                rw[is_succ] at H
                rcases (H q).mp K with K|K; assumption; absurd raa K; trivial
              have := hg.2 q this; rw[K.2] at this
              exact LT.lt.false this
            have eqy' : q'=y := by
              by_contra raa; simp only[raa] at K'; dsimp at K'
              have : IN q' y := by
                have H := H.2; have K' := K'.1
                rw[is_succ] at H
                rcases (H q').mp K' with K|K; assumption; absurd raa K; trivial
              have := hg.2 q' this; rw[K'.2] at this
              exact LT.lt.false this
            rw[eqy, eqy']
      . intro a ax
        by_cases h: (a=y) <;> simp only[h] <;> dsimp
        . norm_num
        . have : IN a y := by
            have H := H.2; rw[is_succ] at H
            rcases (H a).mp ax with K|K; assumption; absurd h K; trivial
          have := hg.2 a this
          exact @Nat.lt_add_right (g a) n 1 this

/-- A set representing the number n in ℕ has cardinality n. --/
theorem number_card' (n : ℕ) : ∀ x, (is_number n x) → ∃f:{a//IN a x}→(Fin n), Function.Bijective f := by
  intro x nx; have nc := number_card n x nx; set f := nc.choose
  set g:{a//IN a x}→ℕ := λa ↦ f (↑a)
  have : ∀a, (g a) < n := by
    intro ⟨a, ha⟩
    show f a < n
    exact nc.choose_spec.2 a ha
  use λa ↦ ⟨g a, this a⟩
  constructor
  . intro ⟨a, ha⟩ ⟨b, hb⟩
    have : (f a = f b) → (a = b) := by
      intro eqa; have eqb : f b = f b := rfl
      have less : f b < n := this ⟨b, hb⟩
      exact (nc.choose_spec.1 (f b) less).unique ⟨ha, eqa⟩ ⟨hb, eqb⟩
    simpa
  . intro ⟨m, hm⟩
    rcases (nc.choose_spec.1 m hm).exists with ⟨a, ha⟩
    use ⟨a, ha.1⟩; have ha := ha.2; simpa

theorem finvert {A B : Type*} : (∃f:A→B, Function.Bijective f) → (∃f:B→A, Function.Bijective f) := by
  intro H; rcases H with ⟨f, H⟩
  use λb ↦ (H.2 b).choose
  constructor
  . intro b b' eq; beta_reduce at eq
    have := (H.2 b').choose_spec
    rw[← eq, (H.2 b).choose_spec] at this
    exact this
  . intro a; use f a
    exact H.1 (H.2 (f a)).choose_spec

theorem prod_bij (x y z : SET.{ℓ}) : (is_prod x y z) → ∃f:({a//IN a x}×{b//IN b y})→{c//IN c z}, Function.Bijective f := by
  intro H; rw[is_prod] at H
  set f:({a//IN a x}×{b//IN b y})→SET.{ℓ} := λc ↦ (couple_ok c.1.1 c.2.1).exists.choose
  have : ∀c, IN (f c) z := by
    intro ⟨⟨a, ha⟩,⟨b, hb⟩⟩
    apply (H _).mpr; use a; use b
    constructor; exact ha
    constructor; exact hb
    exact (couple_ok a b).exists.choose_spec
  use λc ↦ ⟨f c, this c⟩
  constructor
  . intro c d hcd
    have hcd : f c = f d := by
      dsimp at hcd; dsimp
      simp only [Subtype.mk.injEq] at hcd; assumption
    have hc := (couple_ok c.1 c.2).exists.choose_spec
    have hd := (couple_ok d.1 d.2).exists.choose_spec
    change is_couple (↑c.1) (↑c.2) (f c) at hc
    change is_couple (↑d.1) (↑d.2) (f d) at hd
    rw[hcd] at hc
    have := couple_works _ _ _ _ _ hc hd
    ext; exact this.1; exact this.2
  . intro ⟨c, hc⟩
    have H := (H c).mp hc
    rcases H with ⟨a, ⟨b, ⟨ha, ⟨hb, abc⟩⟩⟩⟩
    use ⟨⟨a, ha⟩, ⟨b, hb⟩⟩; ext; dsimp
    exact (couple_ok _ _).unique (couple_ok a b).exists.choose_spec abc

theorem equicard_bij (x y : SET.{ℓ}) : (is_equicard x y) ↔ (∃f:{a//IN a x}→{b//IN b y}, Function.Bijective f) := by
  constructor
  . intro H; rw[is_equicard] at H
    rcases H with ⟨P, ⟨F, ⟨_, ⟨_, ⟨L, R⟩⟩⟩⟩⟩
    set f:{a//IN a x}→SET.{ℓ} := λa ↦ (L a.1 a.2).exists.choose
    have : ∀a, IN (f a) y := λa ↦ (L a.1 a.2).exists.choose_spec.1
    use λa ↦ ⟨f a, this a⟩; constructor
    . intro ⟨a, ha⟩ ⟨a', ha'⟩ H
      have : f ⟨a, ha⟩ = f ⟨a', ha'⟩ := by
        beta_reduce at H; simp only [Subtype.mk.injEq] at H; exact H
      ext; show a=a'
      have spec := (L a ha).exists.choose_spec; set fa := (L a ha).exists.choose
      have spec' := (L a' ha').exists.choose_spec; set fa' := (L a' ha').exists.choose
      change fa = fa' at this
      have R! := R fa spec.1
      have Ra : (IN a x) ∧ (∃ c, (is_couple a fa c) ∧ (IN c F)) := ⟨ha, spec.2⟩
      rw[← this] at spec'
      have Ra' : (IN a' x) ∧ (∃ c, (is_couple a' fa c) ∧ (IN c F)) := ⟨ha', spec'.2⟩
      exact R!.unique Ra Ra'
    . intro ⟨b, hb⟩
      set a := (R b hb).exists.choose with def_a
      have ha : IN a x := (R b hb).exists.choose_spec.1
      use ⟨a, ha⟩; ext; dsimp
      have : (IN b y) ∧ (∃c, (is_couple a b c) ∧ (IN c F)) := by
        constructor; assumption
        use (couple_ok a b).exists.choose
        constructor; exact (couple_ok a b).exists.choose_spec
        have := (R b hb).exists.choose_spec; rw[← def_a] at this
        rcases this.2 with ⟨c, hc⟩
        set c' := (couple_ok a b).exists.choose
        have : c=c' := (couple_ok a b).unique hc.1 (couple_ok a b).exists.choose_spec
        rw[← this]; exact hc.2
      show (L a ha).exists.choose = b
      exact (L a ha).unique (L a ha).exists.choose_spec this
  . intro ⟨f, H⟩; rw[is_equicard]
    have p := prod_ok x y; have hp := p.exists.choose_spec; set P := p.exists.choose; use P
    set F := COMPREHENSION' P (λc ↦ ∃a:{a//IN a x},∃b:{b//IN b y}, (is_couple a b c) ∧ (f a = b))
    rcases F with ⟨F, hF⟩; use F
    constructor; exact hp
    constructor; rw[is_sub]; intro z zin; exact ((hF z).mp zin).1
    constructor
    . intro a ax
      apply existsUnique_of_exists_of_unique
      . use f ⟨a, ax⟩; constructor; exact (f ⟨a, ax⟩).2
        set aa : {a//IN a x} := ⟨a, ax⟩
        have c := couple_ok aa (f aa); have hc := c.exists.choose_spec; set C := c.exists.choose
        use C; constructor; exact hc
        apply (hF C).mpr; constructor
        . rw[is_prod] at hp; apply (hp C).mpr
          use aa; use (f aa); constructor; exact ax
          constructor; exact (f aa).2; exact hc
        . use aa; use (f aa)
      . rintro b b' ⟨bY, ⟨c, ⟨hc, cF⟩⟩⟩ ⟨bY', ⟨c', ⟨hc', cF'⟩⟩⟩
        set aa : {a//IN a x} := ⟨a, ax⟩
        set bb : {b//IN b y} := ⟨b, bY⟩ with bbdef
        set bb': {b//IN b y} := ⟨b', bY'⟩ with bbdef'
        have cF := ((hF c).mp cF).2
        rcases cF with ⟨ak, ⟨bk, ⟨ck, fab⟩⟩⟩
        have := couple_works aa bb ak bk c hc ck
        have ae : aa = ak := by ext; exact this.1
        have be : bb = bk := by ext; exact this.2
        rw [← ae, ← be] at fab
        have cF' := ((hF c').mp cF').2
        rcases cF' with ⟨ak', ⟨bk', ⟨ck', fab'⟩⟩⟩
        have := couple_works aa bb' ak' bk' c' hc' ck'
        have ae : aa  = ak' := by ext; exact this.1
        have be : bb' = bk' := by ext; exact this.2
        rw [← ae, ← be] at fab'
        rw[fab,bbdef,bbdef'] at fab'
        simp only [Subtype.mk.injEq] at fab'; assumption
    . intro b bY
      apply existsUnique_of_exists_of_unique
      . set aa := (H.2 ⟨b, bY⟩).choose; have ha := (H.2 ⟨b, bY⟩).choose_spec; use aa
        constructor; exact aa.2
        set bb : {b//IN b y} := ⟨b, bY⟩
        have c := couple_ok aa bb; have hc := c.exists.choose_spec; set C := c.exists.choose; use C
        constructor; exact hc
        apply (hF C).mpr; constructor
        . rw[is_prod] at hp; apply (hp C).mpr
          use aa; use bb; constructor; exact aa.2
          constructor; exact bb.2; exact hc
        . use aa; use bb
      . rintro a a' ⟨ax, ⟨c, ⟨hc, cF⟩⟩⟩ ⟨ax', ⟨c', ⟨hc', cF'⟩⟩⟩
        set aa : {a//IN a x} := ⟨a, ax⟩ with aadef
        set aa': {a//IN a x} := ⟨a', ax'⟩ with aadef'
        set bb : {b//IN b y} := ⟨b, bY⟩
        have cF := ((hF c).mp cF).2
        rcases cF with ⟨ak, ⟨bk, ⟨ck, fab⟩⟩⟩
        have := couple_works aa bb ak bk c hc ck
        have ae : aa = ak := by ext; exact this.1
        have be : bb = bk := by ext; exact this.2
        rw [← ae, ← be] at fab
        have cF' := ((hF c').mp cF').2
        rcases cF' with ⟨ak', ⟨bk', ⟨ck', fab'⟩⟩⟩
        have := couple_works aa' bb ak' bk' c' hc' ck'
        have ae : aa' = ak' := by ext; exact this.1
        have be : bb  = bk' := by ext; exact this.2
        rw [← ae, ← be] at fab'
        rw[← fab'] at fab
        have := H.1 fab;
        rw[aadef, aadef'] at this
        simp only [Subtype.mk.injEq] at this; assumption



theorem fin_bij (a b : ℕ) : (∃f:(Fin a)→(Fin b), Function.Bijective f) → (a = b) := by
  intro H; rcases H with ⟨f, H⟩
  have := ((Fintype.bijective_iff_injective_and_card f).mp H).2
  rw[Fintype.card_fin, Fintype.card_fin] at this; assumption

theorem fin_prod (a b c : ℕ) : (∃f:((Fin a)×(Fin b))→(Fin c), Function.Bijective f) ↔ (a*b = c) := by
  constructor
  . rintro ⟨f, H⟩
    have := ((Fintype.bijective_iff_surjective_and_card f).mp H).2
    rw[Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin] at this
    exact this
  . intro hc
    set f:((Fin a)×(Fin b))→(Fin c) := λ⟨n,m⟩ ↦ ⟨n*b+m, by
      have hn : ∃k>0, n+k=a := exists_pos_add_of_lt' n.2
      have hm : ∃k>0, n+k=a := exists_pos_add_of_lt' n.2
      rcases hn with ⟨k, ⟨pk, hn⟩⟩; rcases hm with ⟨j, ⟨_, hm⟩⟩
      simp only[← hc, ← hn]; ring_nf
      have d1 : b*1≤b*k := Nat.mul_le_mul_left b pk
      have de : b*1 = b := Nat.mul_one b; rw[de] at d1
      have d2 : m<b*k := Fin.val_lt_of_le m d1
      exact Nat.add_lt_add_left d2 (↑n * b)⟩
    use f
    apply (Fintype.bijective_iff_surjective_and_card f).mpr; constructor
    . intro x
      have pb : b>0 := by
        by_contra raa
        have raa : b=0 := @Nat.eq_zero_of_not_pos b raa
        have raa : c=0 := by rw[raa, mul_zero] at hc; symm; assumption
        absurd x.2; simp only[raa]; exact Nat.not_lt_zero ↑x
      set n := x/b
      have hn : n<a := by
        have hx : x<a*b := by rw[hc]; exact x.2
        exact (Nat.div_lt_iff_lt_mul pb).mpr hx
      set m := x%b
      have hm : m<b := Nat.mod_lt (↑x) pb
      use ⟨⟨n,hn⟩, ⟨m,hm⟩⟩
      dsimp; ext; dsimp; exact Nat.div_add_mod' (↑x) b
    . rwa[Fintype.card_prod, Fintype.card_fin a, Fintype.card_fin b, Fintype.card_fin c]

theorem sum_bij (x y w : SET.{ℓ}) : (is_disj_union x y w) → ∃f:({a//IN a x}⊕{b//IN b y})→{c//IN c w}, Function.Bijective f := by
  intro H; rw[is_disj_union] at H
  have z := zero_ok.exists; have hz := z.choose_spec; set v := z.choose
  have u := one_ok.exists; have hu := u.choose_spec; set o := u.choose
  have sz := single_ok v; have hsz := sz.exists.choose_spec; set vv := sz.exists.choose
  have su := single_ok o; have hsu := su.exists.choose_spec; set oo := su.exists.choose

  rcases H with ⟨x0, ⟨y1, ⟨v', ⟨vv', ⟨o', ⟨oo', H⟩⟩⟩⟩⟩⟩
  have ev : v=v' := zero_ok.unique hz H.2.2.2.2.2.1
  have eo : o=o' := one_ok.unique hu H.2.2.2.2.2.2
  rw[← ev, ← eo] at H
  have evv : vv=vv' := (single_ok v).unique hsz H.2.2.2.1
  have eoo : oo=oo' := (single_ok o).unique hsu H.2.2.2.2.1
  rw[← evv, ← eoo] at H

  have HU := H.1; rw[is_union] at HU
  have HX := H.2.1; rw[is_prod] at HX
  have HY := H.2.2.1; rw[is_prod] at HY

  set f:({a//IN a x}⊕{b//IN b y})→SET.{ℓ} :=
    λ t ↦ match t with
          | .inl a => (couple_ok a v).exists.choose
          | .inr b => (couple_ok b o).exists.choose with fdef
  have : ∀t, IN (f t) w := by
    intro t; match t with
    | .inl a =>
      . show IN (couple_ok a v).exists.choose w
        apply (HU _).mpr; left
        apply (HX _).mpr; use a; use v
        constructor; exact a.2
        constructor
        . rw[is_single, is_pair] at hsz
          exact (hsz v).mpr (Or.inl rfl)
        . exact (couple_ok a v).exists.choose_spec
    | .inr b =>
      . show IN (couple_ok b o).exists.choose w
        apply (HU _).mpr; right
        apply (HY _).mpr; use b; use o
        constructor; exact b.2
        constructor
        . rw[is_single, is_pair] at hsu
          exact (hsu o).mpr (Or.inl rfl)
        . exact (couple_ok b o).exists.choose_spec
  use λt ↦ ⟨f t, this t⟩
  constructor
  . intro t
    match t with
    | .inl a =>
      . intro t'
        match t' with
        | .inl a' =>
          intro eq; simp only[fdef] at eq
          simp only [Subtype.mk.injEq] at eq
          have := couple_works a v a' v
          set az := (couple_ok a v).exists.choose
          have s := (couple_ok a' v).exists.choose_spec; rw[← eq] at s
          have := (this az (couple_ok a v).exists.choose_spec s).1
          simp only [Sum.inl.injEq]
          exact SetCoe.ext this
        | .inr b' =>
          intro eq; simp only[fdef] at eq; exfalso
          simp only [Subtype.mk.injEq] at eq
          set az := (couple_ok a v).exists.choose
          have s := (couple_ok b' o).exists.choose_spec; rw[← eq] at s
          have := ((couple_works _ _ _ _) az (couple_ok a v).exists.choose_spec s).2
          have hz':=hz; rw[this, is_zero] at hz; rw[is_one] at hu
          exact (hz v) ((hu v).mpr hz')
    | .inr b =>
      . intro t'
        match t' with
        | .inl a' =>
          intro eq; simp only[fdef] at eq; exfalso
          simp only [Subtype.mk.injEq] at eq
          set bo := (couple_ok b o).exists.choose
          have s := (couple_ok a' v).exists.choose_spec; rw[← eq] at s
          have := ((couple_works _ _ _ _) bo (couple_ok b o).exists.choose_spec s).2
          symm at this; have hz':=hz; rw[this, is_zero] at hz; rw[is_one] at hu
          exact (hz v) ((hu v).mpr hz')
        | .inr b' =>
          intro eq; simp only[fdef] at eq
          simp only [Subtype.mk.injEq] at eq
          have := couple_works b o b' o
          set az := (couple_ok b o).exists.choose
          have s := (couple_ok b' o).exists.choose_spec; rw[← eq] at s
          have := (this az (couple_ok b o).exists.choose_spec s).1
          simp only [Sum.inr.injEq]
          exact SetCoe.ext this
  . intro c; dsimp; have hc := (HU c).mp c.2
    rcases hc with cx|cy
    . have hx := (HX c).mp cx
      rcases hx with ⟨a, ⟨v'', ⟨ax, ⟨jv, a0c⟩⟩⟩⟩
      rw[is_single, is_pair] at hsz;
      have jv := (hsz v'').mp jv
      have jv : v''=v := by rcases jv with jv|jv <;> exact jv
      rw[jv] at a0c; use .inl ⟨a, ax⟩; dsimp
      ext; exact (couple_ok a v).unique (couple_ok a v).exists.choose_spec a0c
    . have hy := (HY c).mp cy
      rcases hy with ⟨b, ⟨o'', ⟨bY, ⟨jo, b1c⟩⟩⟩⟩
      rw[is_single, is_pair] at hsu;
      have jo := (hsu o'').mp jo
      have jo : o''=o := by rcases jo with jo|jo <;> exact jo
      rw[jo] at b1c; use .inr ⟨b, bY⟩; dsimp
      ext; exact (couple_ok b o).unique (couple_ok b o).exists.choose_spec b1c

theorem fin_sum (a b c : ℕ) : (∃f:((Fin a)⊕(Fin b))→(Fin c), Function.Bijective f) ↔ (a+b = c) := by
  constructor
  . rintro ⟨f, hf⟩
    rw[← Fintype.card_fin a, ← Fintype.card_fin b, ← Fintype.card_fin c, ← Fintype.card_sum]
    exact ((Fintype.bijective_iff_surjective_and_card f).mp hf).2
  . intro hc
    set f:((Fin a)⊕(Fin b))→(Fin c) := λ x ↦ match x with | .inl n => ⟨n, by have := n.2; linarith⟩ | .inr m => ⟨a+m, by have := m.2; linarith⟩; use f
    apply (Fintype.bijective_iff_surjective_and_card f).mpr; constructor
    . intro x; by_cases h: (x<a)
      . use .inl ⟨x, h⟩
      . have : x≥a := Nat.not_lt.mp h
        have : ∃k:ℕ, a+k=x := Nat.le.dest this
        rcases this with ⟨k, this⟩
        use .inr ⟨k, by have := x.2; linarith⟩
        dsimp; ext; exact this
    . rwa[Fintype.card_sum, Fintype.card_fin a, Fintype.card_fin b, Fintype.card_fin c]

theorem sum_of_equiv_is_equiv {A A' B B' : Type*} (ha: ∃f:A→A', Function.Bijective f) (hb: ∃f:B→B', Function.Bijective f) : ∃f:(A⊕B)→(A'⊕B'), Function.Bijective f := by
  rcases ha with ⟨fa, ha⟩
  rcases hb with ⟨fb, hb⟩
  use λc ↦ match c with | .inl a => .inl (fa a) | .inr b => .inr (fb b)
  constructor
  . intro c
    match c with
    | .inl a =>
      . intro c'
        match c' with
        | .inl a' => dsimp; simp only [Sum.inl.injEq]; intro eq; exact ha.1 eq
        | .inr b' => dsimp; intro eq; absurd eq; exact Sum.inl_ne_inr
    | .inr b =>
      . intro c'
        match c' with
        | .inl a' => dsimp; intro eq; absurd eq; exact Sum.inr_ne_inl
        | .inr b' => dsimp; simp only [Sum.inr.injEq]; intro eq; exact hb.1 eq
  . intro c
    match c with
    | .inl a => use .inl (ha.2 a).choose; dsimp; simp only [Sum.inl.injEq]; exact (ha.2 a).choose_spec
    | .inr b => use .inr (hb.2 b).choose; dsimp; simp only [Sum.inr.injEq]; exact (hb.2 b).choose_spec

theorem prod_of_equiv_is_equiv {A A' B B' : Type*} (ha: ∃f:A→A', Function.Bijective f) (hb: ∃f:B→B', Function.Bijective f) : ∃f:(A×B)→(A'×B'), Function.Bijective f := by
  rcases ha with ⟨fa, ha⟩
  rcases hb with ⟨fb, hb⟩
  use λ⟨a, b⟩ ↦ ⟨fa a, fb b⟩
  constructor
  . rintro ⟨a, b⟩ ⟨a', b'⟩ eq
    dsimp at eq; ext <;> dsimp
    . have eq : fa a = fa a' := by
        have := congr_arg (λ(c:A'×B') ↦ c.1) eq
        beta_reduce at this; dsimp at this; assumption
      exact ha.1 eq
    . have eq : fb b = fb b' := by
        have := congr_arg (λ(c:A'×B') ↦ c.2) eq
        beta_reduce at this; dsimp at this; assumption
      exact hb.1 eq
  . rintro ⟨c, d⟩
    use ⟨(ha.2 c).choose, (hb.2 d).choose⟩
    ext <;> dsimp
    . exact (ha.2 c).choose_spec
    . exact (hb.2 d).choose_spec

/-- The sum is well-behaved w.r.t. the bijection ω → ℕ  --/
theorem plus_is_sum : ∀(x y z : SET.{ℓ}), ∀(a b : ℕ), (is_plus x y z) → (is_number a x) → (is_number b y) → (is_number (a+b) z) := by
  intro x y z a b H hx hy
  rw[is_plus] at H; rcases H with ⟨u,H⟩
  have J := sum_bij x y u H.1
  have Fx := number_card' a x hx
  have Fy := number_card' b y hy
  have Fxy := finvert (sum_of_equiv_is_equiv Fx Fy)
  have G := (equicard_bij u z).mp H.2.1
  rcases natural_is_number z H.2.2 with ⟨p, K⟩
  have K := number_card' p z K
  have : ∃f:((Fin a)⊕(Fin b))→(Fin p), Function.Bijective f := by
    rcases Fxy with ⟨fxy, Fxy⟩
    rcases J with ⟨j, J⟩
    rcases G with ⟨g, G⟩
    rcases K with ⟨k, K⟩
    use k∘g∘j∘fxy
    apply Function.Bijective.comp K
    apply Function.Bijective.comp G
    apply Function.Bijective.comp J
    exact Fxy
  rwa[(fin_sum a b p).mp this]

/-- The sum is well-behaved w.r.t. the bijection ℕ → ω --/
theorem sum_is_plus : ∀(x y z : SET.{ℓ}), ∀(a b : ℕ), (is_number a x) → (is_number b y) → (is_number (a+b) z) → (is_plus x y z) := by
  intro x y z a b hx hy hz
  rw[is_plus]; set U := (disj_union_ok x y).exists.choose; use U
  constructor
  . exact (disj_union_ok x y).exists.choose_spec
  . constructor
    . apply (equicard_bij _ _).mpr
      have J := finvert (sum_bij x y U (disj_union_ok x y).exists.choose_spec)
      have Fx := number_card' a x hx
      have Fy := number_card' b y hy
      have Fxy := sum_of_equiv_is_equiv Fx Fy
      have G := (fin_sum a b (a+b)).mpr rfl
      have K := finvert (number_card' (a+b) z hz)
      rcases Fxy with ⟨fxy, Fxy⟩
      rcases J with ⟨j, J⟩
      rcases G with ⟨g, G⟩
      rcases K with ⟨k, K⟩
      use k∘g∘fxy∘j
      apply Function.Bijective.comp K
      apply Function.Bijective.comp G
      apply Function.Bijective.comp Fxy
      exact J
    . exact number_is_natural _ _ hz

/-- The product is well-behaved w.r.t. the bijection ω → ℕ  --/
theorem mult_is_prod : ∀(x y z : SET.{ℓ}), ∀(a b : ℕ), (is_mult x y z) → (is_number a x) → (is_number b y) → (is_number (a*b) z) := by
  intro x y z a b H hx hy
  rw[is_mult] at H; rcases H with ⟨u,H⟩
  have J := prod_bij x y u H.1
  have Fx := number_card' a x hx
  have Fy := number_card' b y hy
  have Fxy := finvert (prod_of_equiv_is_equiv Fx Fy)
  have G := (equicard_bij u z).mp H.2.1
  rcases natural_is_number z H.2.2 with ⟨p, K⟩
  have K := number_card' p z K
  have : ∃f:((Fin a)×(Fin b))→(Fin p), Function.Bijective f := by
    rcases Fxy with ⟨fxy, Fxy⟩
    rcases J with ⟨j, J⟩
    rcases G with ⟨g, G⟩
    rcases K with ⟨k, K⟩
    use k∘g∘j∘fxy
    apply Function.Bijective.comp K
    apply Function.Bijective.comp G
    apply Function.Bijective.comp J
    exact Fxy
  rwa[(fin_prod a b p).mp this]

/-- The product is well-behaved w.r.t. the bijection ℕ → ω --/
theorem prod_is_mult : ∀(x y z : SET.{ℓ}), ∀(a b : ℕ), (is_number a x) → (is_number b y) → (is_number (a*b) z) → (is_mult x y z) := by
  intro x y z a b hx hy hz
  rw[is_mult]; set U := (prod_ok x y).exists.choose; use U
  constructor
  . exact (prod_ok x y).exists.choose_spec
  . constructor
    . apply (equicard_bij _ _).mpr
      have J := finvert (prod_bij x y U (prod_ok x y).exists.choose_spec)
      have Fx := number_card' a x hx
      have Fy := number_card' b y hy
      have Fxy := prod_of_equiv_is_equiv Fx Fy
      have G := (fin_prod a b (a*b)).mpr rfl
      have K := finvert (number_card' (a*b) z hz)
      rcases Fxy with ⟨fxy, Fxy⟩
      rcases J with ⟨j, J⟩
      rcases G with ⟨g, G⟩
      rcases K with ⟨k, K⟩
      use k∘g∘fxy∘j
      apply Function.Bijective.comp K
      apply Function.Bijective.comp G
      apply Function.Bijective.comp Fxy
      exact J
    . exact number_is_natural _ _ hz

/-- The successor is well-behaved w.r.t. the bijection ω ↔ ℕ  --/
theorem succ_is_succ : ∀(x y : SET.{ℓ}), ∀a:ℕ, (is_succ x y) → (is_number a x) → (is_number (a+1) y) := by
  intro x y a H hx
  rw[is_number]; use x

/-- A type to code the syntactic content of *first*-order terms in the language of Peano. --/
inductive AriTerm where
| O : AriTerm
| Var : ℕ → AriTerm
| Succ : AriTerm → AriTerm
| Plus : AriTerm → AriTerm → AriTerm
| Mult : AriTerm → AriTerm → AriTerm
open AriTerm

def term_to_nat (f: ℕ → ℕ) (t : AriTerm) : ℕ :=
  match t with
  | O => 0
  | Var n => f n
  | Succ t => Nat.succ (term_to_nat f t)
  | Plus t s => (term_to_nat f t) + (term_to_nat f s)
  | Mult t s => (term_to_nat f t) * (term_to_nat f s)

def is_term (f: ℕ → SET.{ℓ}) (t : AriTerm) (x : SET.{ℓ}) : Prop :=
  match t with
  | O => is_zero x
  | Var n => f n = x
  | Succ t => ∃y, (is_term f t y) ∧ (is_succ y x)
  | Plus t s => ∃y, ∃z, (is_term f t y) ∧ (is_term f s z) ∧ (is_plus y z x)
  | Mult t s => ∃y, ∃z, (is_term f t y) ∧ (is_term f s z) ∧ (is_mult y z x)

def is_free_t (t: AriTerm) (v : ℕ) : Prop :=
  match t with
  | O  => ⊥
  | Var w => v=w
  | Succ t => is_free_t t v
  | Plus t s | Mult t s => (is_free_t t v) ∨ (is_free_t s v)

def is_faithful_t (f: ℕ → ℕ) (g: ℕ → SET.{ℓ}) (t:AriTerm) : Prop :=
  ∀v, (is_free_t t v) → (is_number (f v) (g v))

/-- All terms have the same meaning when seen as a over ℕ or over ω
(if the free variables are interpreted in a compatible manner). --/
theorem is_term_iff_is_number (f: ℕ → ℕ) (g: ℕ → SET.{ℓ}) (t : AriTerm) (faith: is_faithful_t f g t): ∀x, (is_term g t x) ↔ (is_number (term_to_nat f t) x) := by
  intro x; match t with
  | O => rw[is_term, term_to_nat, is_number];
  | Var n =>
    . rw[is_term, term_to_nat]; rw[is_faithful_t] at faith
      constructor
      . intro h; rw[← h]
        have faith := faith n
        rw[is_free_t] at faith
        exact faith rfl
      . intro h
        have faith := faith n (by rw[is_free_t])
        exact (number_ok (f n)).unique faith h
  | Succ t =>
    . rw[is_term, term_to_nat, is_number]
      constructor
      . rintro ⟨y, h⟩; use y; constructor
        . exact (is_term_iff_is_number f g t faith y).mp h.1
        . exact h.2
      . rintro ⟨y, h⟩; use y; constructor
        . exact (is_term_iff_is_number f g t faith y).mpr h.1
        . exact h.2
  | Plus t s =>
    . rw[is_term, term_to_nat]
      have ft : ∀ (v : ℕ), is_free_t t v → is_number (f v) (g v) := by
        intro v hv; have faith := faith v; rw[is_free_t] at faith
        exact faith (Or.inl hv)
      have fs : ∀ (v : ℕ), is_free_t s v → is_number (f v) (g v) := by
        intro v hv; have faith := faith v; rw[is_free_t] at faith
        exact faith (Or.inr hv)
      constructor
      . rintro ⟨y, ⟨z, h⟩⟩
        rw[is_faithful_t] at faith
        have hy := (is_term_iff_is_number f g t ft y).mp h.1
        have hz := (is_term_iff_is_number f g s fs z).mp h.2.1
        exact plus_is_sum y z x _ _ h.2.2 hy hz
      . intro h
        have yd := number_ok (term_to_nat f t); set y := yd.exists.choose
        have zd := number_ok (term_to_nat f s); set z := zd.exists.choose
        use y; use z; constructor
        . exact (is_term_iff_is_number f g t ft y).mpr yd.exists.choose_spec
        constructor
        . exact (is_term_iff_is_number f g s fs z).mpr zd.exists.choose_spec
        . exact sum_is_plus _ _ _ _ _ yd.exists.choose_spec zd.exists.choose_spec h
  | Mult t s =>
    . rw[is_term, term_to_nat]
      have ft : ∀ (v : ℕ), is_free_t t v → is_number (f v) (g v) := by
        intro v hv; have faith := faith v; rw[is_free_t] at faith
        exact faith (Or.inl hv)
      have fs : ∀ (v : ℕ), is_free_t s v → is_number (f v) (g v) := by
        intro v hv; have faith := faith v; rw[is_free_t] at faith
        exact faith (Or.inr hv)
      constructor
      . rintro ⟨y, ⟨z, h⟩⟩
        rw[is_faithful_t] at faith
        have hy := (is_term_iff_is_number f g t ft y).mp h.1
        have hz := (is_term_iff_is_number f g s fs z).mp h.2.1
        exact mult_is_prod y z x _ _ h.2.2 hy hz
      . intro h
        have yd := number_ok (term_to_nat f t); set y := yd.exists.choose
        have zd := number_ok (term_to_nat f s); set z := zd.exists.choose
        use y; use z; constructor
        . exact (is_term_iff_is_number f g t ft y).mpr yd.exists.choose_spec
        constructor
        . exact (is_term_iff_is_number f g s fs z).mpr zd.exists.choose_spec
        . exact prod_is_mult _ _ _ _ _ yd.exists.choose_spec zd.exists.choose_spec h

theorem eqnum (n n':ℕ) (x:SET.{ℓ}) : (is_number n x) → (is_number n' x) → (n=n') := by
  intro hx hx'
  rcases finvert (number_card' _ _ hx) with ⟨j1, hx⟩
  rcases number_card' _ _ hx' with ⟨j2, hx'⟩
  have : ∃j:(Fin n)→(Fin n'), Function.Bijective j := by
    use j2∘j1; exact Function.Bijective.comp hx' hx
  exact fin_bij n n' this

def is_sub_nat (A: SET.{ℓ}) := ∃ω, (is_omega ω) ∧ (is_sub A ω)
def is_real (f: Set ℕ) (A: SET.{ℓ}) :=
  (∀x,((IN x A) ↔ (∃n, (is_number n x) ∧ (f n))))

theorem real_ok (f: Set ℕ) : ∃!A, (is_real f A) := by
  apply existsUnique_of_exists_of_unique
  . rcases omega_ok.exists with ⟨ω, hw⟩
    simp only[is_real]
    rcases COMPREHENSION' ω (λc ↦ ∃n, (is_number n c) ∧ (f n)) with ⟨A, hA⟩
    use A; intro z; constructor
    . intro zA; exact ((hA z).mp zA).2
    . intro hz; have hA := (hA z).mpr
      rcases hz with ⟨n, ⟨hn, fn⟩⟩
      have hn' := number_is_natural n z hn
      rw[is_natural] at hn'
      rcases hn' with ⟨ω', hn'⟩
      have : ω'=ω := omega_ok.unique hn'.1 hw; rw[this] at hn'
      apply hA; constructor; exact hn'.2; use n
  . intro y y' hy hy'; apply EXTENSIONALITY
    intro z; constructor
    . intro zy; rw[is_real] at *
      exact (hy' z).mpr ((hy z).mp zy)
    . intro zy'; rw[is_real] at *
      exact (hy z).mpr ((hy' z).mp zy')
theorem real_is_sub_nat (f: Set ℕ) : ∀A, (is_real f A) → (is_sub_nat A) := by
  intro A hA
  rw[is_sub_nat, is_real] at *
  rcases omega_ok.exists with ⟨ω, hw⟩
  use ω; constructor; assumption
  intro z zA
  rcases (hA z).mp zA with ⟨n, ⟨hA, _⟩⟩
  have hA := number_is_natural _ _ hA
  rw[is_natural] at hA; rcases hA with ⟨ω', hA⟩
  have : ω'=ω := omega_ok.unique hA.1 hw; rw[this] at hA
  exact hA.2
theorem sub_nat_is_real : ∀A, (is_sub_nat A) → ∃!f, (is_real f A) := by
  intro A hA
  simp only[is_sub_nat, is_real] at *
  rcases hA with ⟨ω, ⟨hw, hA⟩⟩
  apply existsUnique_of_exists_of_unique
  . use (λ n ↦ ∃y, (is_number n y) ∧ (IN y A))
    intro x; constructor
    . intro xA; have hx := hA _ xA
      have hx : is_natural x := by
        rw[is_natural]; use ω
      rcases natural_is_number _ hx with ⟨n, hx⟩
      use n; constructor; assumption; use x
    . intro ⟨n, ⟨hx, ⟨y, ⟨hy, yA⟩⟩⟩⟩
      have : x=y := (number_ok _).unique hx hy
      rw[this]; assumption
  . intro f f' hf hf'
    apply funext; intro n; apply propext
    constructor
    . intro fn
      rcases (number_ok n).exists with ⟨x, hx⟩
      rcases (hf' x).mp ((hf x).mpr ⟨n, ⟨hx, fn⟩⟩) with ⟨n', ⟨hx', fn'⟩⟩
      rw[eqnum _ _ _ hx hx']; assumption
    . intro fn'
      rcases (number_ok n).exists with ⟨x, hx⟩
      rcases (hf x).mp ((hf' x).mpr ⟨n, ⟨hx, fn'⟩⟩) with ⟨n', ⟨hx', fn'⟩⟩
      have : n=n' := by
        rcases finvert (number_card' _ _ hx) with ⟨j1, hx⟩
        rcases number_card' _ _ hx' with ⟨j2, hx'⟩
        have : ∃j:(Fin n)→(Fin n'), Function.Bijective j := by
          use j2∘j1; exact Function.Bijective.comp hx' hx
        exact fin_bij n n' this
      rw[this]; assumption

theorem fZ_is_fL : ∀(A x: SET.{ℓ}), ∀n:ℕ, ∀f:Set ℕ, (IN x A) → (is_number n x) → (is_real f A) → (f n) := by
  intro A x n f xA nx fA
  rcases (fA x).mp xA with ⟨n', ⟨nx', fn⟩⟩
  rw[eqnum _ _ _ nx nx']; assumption

theorem fL_is_fZ : ∀(A x: SET.{ℓ}), ∀n:ℕ, ∀f:Set ℕ, (f n) → (is_number n x) → (is_real f A) → (IN x A) := by
  intro A x n f xA nx fA
  apply (fA x).mpr; use n


/-- A type to code the syntactic content of *second*-order terms in the language of Peano. --/
inductive AriTerm2 where
| Var2 : ℕ → AriTerm2
open AriTerm2

/-- A type to code the syntactic content of second-order formulas in the language of Peano. --/
inductive AriFormula2 where
| Eq : AriTerm → AriTerm → AriFormula2
| Fun: AriTerm2 → AriTerm → AriFormula2
| F : AriFormula2
| Then : AriFormula2 → AriFormula2 → AriFormula2
| Any : ℕ → AriFormula2 → AriFormula2
| Any2: ℕ → AriFormula2 → AriFormula2
infix:52 "⇒" => AriFormula2.Then
infix:60 "≅" => AriFormula2.Eq
notation:max "⊥f"=> AriFormula2.F
notation:max "E" n "," φ => AriFormula2.Any n φ
notation:max "E₂" n "," φ => AriFormula2.Any2 n φ

def term2_to_real (f: ℕ → Set ℕ) (t : AriTerm2) : Set ℕ :=
  match t with
  | Var2 n => f n

def is_term2 (f: ℕ → SET.{ℓ}) (t : AriTerm2) (x : SET.{ℓ}) : Prop :=
  match t with
  | Var2 n => f n = x

def is_free_t2 (t: AriTerm2) (v : ℕ) : Prop :=
  match t with
  | Var2 w => v=w

def is_faithful_t2 (f: ℕ → Set ℕ) (g: ℕ → SET.{ℓ}) (t:AriTerm2) : Prop :=
  ∀v, (is_free_t2 t v) → (is_real (f v) (g v))

theorem is_term2_iff_is_real (f: ℕ → Set ℕ) (g: ℕ → SET.{ℓ}) (t : AriTerm2) (faith: is_faithful_t2 f g t):
    ∀x, (is_term2 g t x) ↔ (is_real (term2_to_real f t) x) := by
  intro x; constructor <;> intro H
  . match t with
    | Var2 n =>
      . rw[is_term2, term2_to_real, is_faithful_t2] at *;
        have faith := faith n (by rw[is_free_t2])
        rw[← H]; assumption
  . match t with
    | Var2 n =>
      . rw[is_term2, term2_to_real, is_faithful_t2] at *;
        have faith := faith n (by rw[is_free_t2])
        exact (real_ok _).unique faith H

/-- This is the function that operates the translation φ ↦ φ_C --/
def AriFormula2_to_Lean' (f:ℕ → ℕ) (f2:ℕ → Set ℕ) (φ: AriFormula2) : Prop :=
  match φ with
  | .F => ⊥
  | .Eq t s => (term_to_nat f t)=(term_to_nat f s)
  | .Fun t s => (term2_to_real f2 t) (term_to_nat f s)
  | .Then t s => (AriFormula2_to_Lean' f f2 t) → (AriFormula2_to_Lean' f f2 s)
  | .Any v ψ => ∃n, AriFormula2_to_Lean' (patch f v n) f2 ψ
  | .Any2 v ψ => ∃g, AriFormula2_to_Lean' f (patch f2 v g) ψ

def AriFormula2_to_Lean (φ: AriFormula2) : Prop := ∀f, ∀f2, AriFormula2_to_Lean' f f2 φ

/-- This is the function that operates the translation φ ↦ (φ_Z)_M --/
def AriFormula2_to_ZFC'.{u} (f f2:ℕ → SET.{u}) (φ: AriFormula2) : Prop :=
  match φ with
  | .F => ⊥
  | .Eq t s => ∃x, (is_term f t x) ∧ (is_term f s x)
  | .Fun t s => ∃A,∃x, (is_term2 f2 t A) ∧ (is_term f s x) ∧ (IN x A)
  | .Then t s => (AriFormula2_to_ZFC' f f2 t) → (AriFormula2_to_ZFC' f f2 s)
  | .Any v ψ => ∃n, (is_natural n) ∧ (AriFormula2_to_ZFC' (patch f v n) f2 ψ)
  | .Any2 v ψ => ∃A, (is_sub_nat A) ∧ (AriFormula2_to_ZFC' f (patch f2 v A) ψ)

def AriFormula2_to_ZFC.{u} (φ: AriFormula2) : Prop := ∀f, ∀f2, AriFormula2_to_ZFC'.{u} f f2 φ

def is_free (φ: AriFormula2) (v : ℕ) : Prop :=
  match φ with
  | .F => ⊥
  | .Eq t s => (is_free_t t v) ∨ (is_free_t s v)
  | .Fun _ s => (is_free_t s v)
  | .Then φ ψ => (is_free φ v) ∨ (is_free ψ v)
  | .Any w ψ => ite (v=w : Prop) ⊥ (is_free ψ v)
  | .Any2 _ ψ => is_free ψ v

def is_free2 (φ: AriFormula2) (v : ℕ) : Prop :=
  match φ with
  | .F | .Eq _ _ => ⊥
  | .Fun f _ => (is_free_t2 f v)
  | .Then φ ψ => (is_free2 φ v) ∨ (is_free2 ψ v)
  | .Any _ ψ => is_free2 ψ v
  | .Any2 f ψ => ite (v=f : Prop) ⊥ (is_free2 ψ v)

def is_faithful.{u} (f: ℕ → ℕ) (f2: ℕ → Set ℕ) (g: ℕ → SET.{u}) (g2: ℕ → SET.{u}) (φ: AriFormula2) : Prop :=
  (∀v, (is_free φ v) → (is_number (f v) (g v))) and
  (∀v, (is_free2 φ v) → (is_real (f2 v) (g2 v)))


def is_sentence (φ: AriFormula2) : Prop := (¬∃v, is_free φ v) ∧ (¬∃v, is_free2 φ v)
def is_pure_term (t: AriTerm) : Prop := ¬∃v, is_free_t t v
def is_pure_term2 (t: AriTerm2) : Prop := ¬∃v, is_free_t2 t v

theorem nonfree_irrelevance_Lean_term (f g:ℕ → ℕ) (t : AriTerm) :
    (∀v, (is_free_t t v) → (f v = g v)) → ((term_to_nat f t) = (term_to_nat g t)) := by
  intro H; match t with
  | O  =>  rw[term_to_nat, term_to_nat]
  | Var v =>
    . have H := H v; rw[is_free_t] at H
      rw[term_to_nat, term_to_nat]; exact H rfl
  | Plus t s | Mult t s =>
    . rw[term_to_nat, term_to_nat]
      have Ht : ∀ (v : ℕ), is_free_t t v → f v = g v := by
        intro v hv; have H := H v; rw[is_free_t] at H
        exact H (Or.inl hv)
      have Hs : ∀ (v : ℕ), is_free_t s v → f v = g v := by
        intro v hv; have H := H v; rw[is_free_t] at H
        exact H (Or.inr hv)
      rw[nonfree_irrelevance_Lean_term f g t Ht]
      rw[nonfree_irrelevance_Lean_term f g s Hs]
  | Succ t =>
    . rw[term_to_nat, term_to_nat]
      have Ht : ∀ (v : ℕ), is_free_t t v → f v = g v := by
        intro v hv; have H := H v; rw[is_free_t] at H
        exact H hv
      rw[nonfree_irrelevance_Lean_term f g t Ht]

theorem nonfree_irrelevance_Lean_term2 (f g: ℕ → Set ℕ) (t : AriTerm2) :
    (∀v, (is_free_t2 t v) → (f v = g v)) → ((term2_to_real f t) = (term2_to_real g t)) := by
  intro H; match t with
  | Var2 n =>
    . rw[term2_to_real, term2_to_real];
      apply H n; rw[is_free_t2]


theorem nonfree_irrelevance_ZFC_term.{u} (f g:ℕ → SET.{u}) (t : AriTerm) :
    (∀v, (is_free_t t v) → (f v = g v)) → (∀x, (is_term f t x) ↔ (is_term g t x)) := by
  intro H x; match t with
  | O  =>  rw[is_term, is_term]
  | Var v =>
    . have H := H v; rw[is_free_t] at H
      rw[is_term, is_term]; rw[H rfl]
  | Plus t s | Mult t s =>
    . rw[is_term, is_term]
      have Ht : ∀ (v : ℕ), is_free_t t v → f v = g v := by
        intro v hv; have H := H v; rw[is_free_t] at H
        exact H (Or.inl hv)
      have Hs : ∀ (v : ℕ), is_free_t s v → f v = g v := by
        intro v hv; have H := H v; rw[is_free_t] at H
        exact H (Or.inr hv)
      simp only[nonfree_irrelevance_ZFC_term f g t Ht]
      simp only[nonfree_irrelevance_ZFC_term f g s Hs]
  | Succ t =>
    . rw[is_term, is_term]
      have Ht : ∀ (v : ℕ), is_free_t t v → f v = g v := by
        intro v hv; have H := H v; rw[is_free_t] at H
        exact H hv
      simp only[nonfree_irrelevance_ZFC_term f g t Ht]

theorem nonfree_irrelevance_ZFC_term2.{u} (f g:ℕ → SET.{u}) (t : AriTerm2) :
    (∀v, (is_free_t2 t v) → (f v = g v)) → (∀x, (is_term2 f t x) ↔ (is_term2 g t x)) := by
  intro H x; match t with
  | Var2 n =>
    . rw[is_term2, is_term2];
      rw[H n (by rw[is_free_t2])]


set_option maxHeartbeats 2000000
theorem nonfree_irrelevance_Lean2 (f :ℕ → ℕ) (f2: ℕ → Set ℕ) (g: ℕ → ℕ) (g2: ℕ → Set ℕ) (φ: AriFormula2) :
    (∀v, (is_free φ v) → (f v = g v)) → (∀v, (is_free2 φ v) → (f2 v = g2 v)) →
    ((AriFormula2_to_Lean' f f2 φ) → (AriFormula2_to_Lean' g g2 φ)) := by
  intro H J hf
  match φ with
  | .F => absurd hf; simp only[AriFormula2_to_Lean']; trivial
  | .Then φ ψ =>
    . simp only[AriFormula2_to_Lean'] at *
      have H1 : ∀v, (is_free φ v) → (g v = f v) := by
        intro v hv; symm
        have : is_free (φ⇒ψ) v := by rw[is_free]; exact Or.inl hv
        exact H v this
      have H2 : ∀v, (is_free ψ v) → (f v = g v) := by
        intro v hv
        have : is_free (φ⇒ψ) v := by rw[is_free]; exact Or.inr hv
        exact H v this
      have J1 : ∀v, (is_free2 φ v) → (g2 v = f2 v) := by
        intro v hv; symm
        have : is_free2 (φ⇒ψ) v := by rw[is_free2]; exact Or.inl hv
        exact J v this
      have J2 : ∀v, (is_free2 ψ v) → (f2 v = g2 v) := by
        intro v hv
        have : is_free2 (φ⇒ψ) v := by rw[is_free2]; exact Or.inr hv
        exact J v this
      intro hg1; have hg1 := nonfree_irrelevance_Lean2 g g2 f f2 φ H1 J1 hg1
      exact nonfree_irrelevance_Lean2 f f2 g g2 ψ H2 J2 (hf hg1)
  | .Eq t s =>
    . rw[AriFormula2_to_Lean'] at *
      have Ht : ∀ (v : ℕ), is_free_t t v → f v = g v := by
        intro v hv; have H := H v; rw[is_free] at H
        exact H (Or.inl hv)
      have Hs : ∀ (v : ℕ), (is_free_t s v) → (f v = g v) := by
        intro v hv; have H := H v; rw[is_free] at H
        exact H (Or.inr hv)
      rw[← nonfree_irrelevance_Lean_term f g t Ht]
      rw[← nonfree_irrelevance_Lean_term f g s Hs]
      assumption
  | .Fun fz t =>
    . rw[AriFormula2_to_Lean'] at *
      have Ht : ∀ (v : ℕ), is_free_t t v → f v = g v := by
        intro v hv; have H := H v; rw[is_free] at H
        exact H hv
      rw[← nonfree_irrelevance_Lean_term f g t Ht]
      have Hfz : ∀ (v : ℕ), is_free_t2 fz v → f2 v = g2 v := by
        intro v hv; have J := J v; rw[is_free2] at J
        exact J hv
      rw[← nonfree_irrelevance_Lean_term2 f2 g2 fz Hfz]
      assumption
  | .Any v ψ =>
    . simp only[AriFormula2_to_Lean'] at *
      rcases hf with ⟨n, hf⟩; use n
      have H' : ∀w, (is_free ψ w) → ((patch f v n w) = (patch g v n w)) := by
        intro w; by_cases h: (w=v : Prop)
        <;> intro hw <;> rw[patch, patch] <;> simp only[h] <;> dsimp
        have H := H w; simp only[is_free, h] at H; dsimp at H
        exact H hw
      exact nonfree_irrelevance_Lean2 (patch f v n) f2 (patch g v n) g2 ψ H' J hf
  | .Any2 v ψ =>
    . simp only[AriFormula2_to_Lean'] at *
      rcases hf with ⟨n, hf⟩; use n
      have J' : ∀w, (is_free2 ψ w) → ((patch f2 v n w) = (patch g2 v n w)) := by
        intro w; by_cases h: (w=v : Prop)
        <;> intro hw <;> rw[patch, patch] <;> simp only[h] <;> dsimp
        have J := J w; simp only[is_free2, h] at J; dsimp at J
        exact J hw
      exact nonfree_irrelevance_Lean2 f (patch f2 v n) g (patch g2 v n) ψ H J' hf

theorem nonfree_irrelevance_ZFC2.{u} (f f2 g g2:ℕ → SET.{u}) (φ: AriFormula2) :
    (∀v, (is_free φ v) → (f v = g v)) → (∀v, (is_free2 φ v) → (f2 v = g2 v)) →
    ((AriFormula2_to_ZFC' f f2 φ) → (AriFormula2_to_ZFC' g g2 φ)) := by
  intro H J hf
  match φ with
  | ⊥f => absurd hf; simp only[AriFormula2_to_ZFC']; trivial
  | .Then φ ψ =>
    . simp only[AriFormula2_to_ZFC'] at *
      have H1 : ∀v, (is_free φ v) → (g v = f v) := by
        intro v hv; symm
        have : is_free (φ⇒ψ) v := by rw[is_free]; exact Or.inl hv
        exact H v this
      have H2 : ∀v, (is_free ψ v) → (f v = g v) := by
        intro v hv
        have : is_free (φ⇒ψ) v := by rw[is_free]; exact Or.inr hv
        exact H v this
      have J1 : ∀v, (is_free2 φ v) → (g2 v = f2 v) := by
        intro v hv; symm
        have : is_free2 (φ⇒ψ) v := by rw[is_free2]; exact Or.inl hv
        exact J v this
      have J2 : ∀v, (is_free2 ψ v) → (f2 v = g2 v) := by
        intro v hv
        have : is_free2 (φ⇒ψ) v := by rw[is_free2]; exact Or.inr hv
        exact J v this
      intro hg1; have hg1 := nonfree_irrelevance_ZFC2 g g2 f f2 φ H1 J1 hg1
      exact nonfree_irrelevance_ZFC2 f f2 g g2 ψ H2 J2 (hf hg1)
  | .Any v ψ =>
    . simp only[AriFormula2_to_ZFC'] at *
      rcases hf with ⟨n, hf⟩; use n
      have H' : ∀w, (is_free ψ w) → ((patch f v n w) = (patch g v n w)) := by
        intro w; by_cases h: (w=v : Prop)
        <;> intro hw <;> rw[patch, patch] <;> simp only[h] <;> dsimp
        have H := H w; simp only[is_free, h] at H; dsimp at H
        exact H hw
      exact ⟨hf.1, nonfree_irrelevance_ZFC2 (patch f v n) f2 (patch g v n) g2 ψ H' J hf.2⟩
  | .Any2 v ψ =>
    . simp only[AriFormula2_to_ZFC'] at *
      rcases hf with ⟨n, hf⟩; use n
      have J' : ∀w, (is_free2 ψ w) → ((patch f2 v n w) = (patch g2 v n w)) := by
        intro w; by_cases h: (w=v : Prop)
        <;> intro hw <;> rw[patch, patch] <;> simp only[h] <;> dsimp
        have J := J w; simp only[is_free2, h] at J; dsimp at J
        exact J hw
      exact ⟨hf.1, nonfree_irrelevance_ZFC2 f (patch f2 v n) g (patch g2 v n) ψ H J' hf.2⟩
  | .Eq t s =>
    rw[AriFormula2_to_ZFC'] at *
    have Ht : ∀ (v : ℕ), is_free_t t v → f v = g v := by
      intro v hv; have H := H v; rw[is_free] at H
      exact H (Or.inl hv)
    have Hs : ∀ (v : ℕ), is_free_t s v → f v = g v := by
        intro v hv; have H := H v; rw[is_free] at H
        exact H (Or.inr hv)
    simp only[← nonfree_irrelevance_ZFC_term f g t Ht]
    simp only[← nonfree_irrelevance_ZFC_term f g s Hs]
    assumption
  | .Fun fz t =>
    rw[AriFormula2_to_ZFC'] at *
    rcases hf with ⟨A, ⟨x, ⟨hfz, ⟨ht, xA⟩⟩⟩⟩; use A; use x
    constructor
    . have : ∀v, (is_free_t2 fz v) → (f2 v = g2 v) := by
        intro v hv; have J := J v; rw[is_free2] at J
        exact J hv
      rw[← nonfree_irrelevance_ZFC_term2 f2 g2 fz this]; assumption
    constructor
    . have Ht : ∀ (v : ℕ), is_free_t t v → f v = g v := by
        intro v hv; have H := H v; rw[is_free] at H
        exact H hv
      rw[← nonfree_irrelevance_ZFC_term f g t Ht]; assumption
    . assumption

theorem sentence_valuation.{u} (φ: AriFormula2) (H: is_sentence φ) :
    (∀f,∀f2,∀g,∀g2, (AriFormula2_to_Lean' f f2 φ) ↔ (AriFormula2_to_Lean' g g2 φ)) ∧
    (∀f,∀f2,∀g,∀g2, (AriFormula2_to_ZFC'.{u}  f f2 φ) ↔ (AriFormula2_to_ZFC'.{u}  g g2 φ)) ∧
    (∀f,∀f2,∀g,∀g2, is_faithful.{u} f f2 g g2 φ) := by
  constructor
  . intro f f2 g g2
    have no_free_vars : ∀(f g: ℕ → ℕ), ∀v, (is_free φ v) → (f v = g v) := by
      intro _ _ v hv; exfalso
      rw[is_sentence] at H
      exact forall_not_of_not_exists H.1 v hv
    have no_free_vars2 : ∀(f g: ℕ → Set ℕ), ∀v, (is_free2 φ v) → (f v = g v) := by
      intro _ _ v hv; exfalso
      rw[is_sentence] at H
      exact forall_not_of_not_exists H.2 v hv
    exact ⟨nonfree_irrelevance_Lean2 f f2 g g2 φ (no_free_vars f g) (no_free_vars2 f2 g2),
           nonfree_irrelevance_Lean2 g g2 f f2 φ (no_free_vars g f) (no_free_vars2 g2 f2)⟩
  constructor
  . intro f f2 g g2
    have no_free_vars : ∀(f g: ℕ → SET.{u}), ∀v, (is_free φ v) → (f v = g v) := by
      intro _ _ v hv; exfalso
      rw[is_sentence] at H
      exact forall_not_of_not_exists H.1 v hv
    have no_free_vars2 : ∀(f g: ℕ → SET.{u}), ∀v, (is_free2 φ v) → (f v = g v) := by
      intro _ _ v hv; exfalso
      rw[is_sentence] at H
      exact forall_not_of_not_exists H.2 v hv
    exact ⟨nonfree_irrelevance_ZFC2 f f2 g g2 φ (no_free_vars f g) (no_free_vars2 f2 g2),
           nonfree_irrelevance_ZFC2 g g2 f f2 φ (no_free_vars g f) (no_free_vars2 g2 f2)⟩
  . intro f f2 g g2
    rw[is_faithful]; rw[is_sentence] at H; constructor
    . intro v hv; exfalso; exact forall_not_of_not_exists H.1 v hv
    . intro v hv; exfalso; exact forall_not_of_not_exists H.2 v hv

theorem ZFC_iff_Lean'.{u} (f: ℕ → ℕ) (f2: ℕ → Set ℕ) (g g2: ℕ → SET.{u}) (φ: AriFormula2) (faith: is_faithful.{u} f f2 g g2 φ) :
    (AriFormula2_to_ZFC'.{u} g g2 φ) ↔ (AriFormula2_to_Lean' f f2 φ) := by
  match φ with
  | ⊥f => rw[AriFormula2_to_ZFC', AriFormula2_to_Lean']
  | .Then φ ψ =>
    . rw[AriFormula2_to_ZFC', AriFormula2_to_Lean']
      have hf1 : ∀ (v : ℕ), is_free φ v → is_number (f v) (g v) := by
        intro v hv; have faith := faith.1 v; rw[is_free] at faith
        exact faith (Or.inl hv)
      have hf2 : ∀ (v : ℕ), is_free ψ v → is_number (f v) (g v) := by
        intro v hv; have faith := faith.1 v; rw[is_free] at faith
        exact faith (Or.inr hv)
      have jf1 : ∀ (v : ℕ), is_free2 φ v → is_real (f2 v) (g2 v) := by
        intro v hv; have faith := faith.2 v; rw[is_free2] at faith
        exact faith (Or.inl hv)
      have jf2 : ∀ (v : ℕ), is_free2 ψ v → is_real (f2 v) (g2 v) := by
        intro v hv; have faith := faith.2 v; rw[is_free2] at faith
        exact faith (Or.inr hv)
      rw[ZFC_iff_Lean' f f2 g g2 φ ⟨hf1, jf1⟩, ZFC_iff_Lean' f f2 g g2 ψ ⟨hf2, jf2⟩]
  | .Any v ψ =>
    . rw[AriFormula2_to_ZFC', AriFormula2_to_Lean']; constructor
      . intro H; rcases H with ⟨N, ⟨hN, H⟩⟩
        rcases (natural_is_number N hN) with ⟨n, hN⟩; use n
        have faith : is_faithful (patch f v n) f2 (patch g v N) g2 ψ := by
          rw[is_faithful]; constructor; intro w hw
          by_cases h: (w=v : Prop)
          . simp only[patch, h]; dsimp; assumption
          . simp only[patch, h]; dsimp
            rw[is_faithful] at faith
            have faith := faith.1 w; simp only[is_free, h] at faith
            dsimp at faith; exact faith hw
          exact faith.2
        exact (ZFC_iff_Lean' _ _ _ _ ψ faith).mp H
      . intro ⟨n, H⟩; set N := (number_ok n).exists.choose; use N
        constructor
        . exact number_is_natural _ _ (number_ok n).exists.choose_spec
        . have faith : is_faithful (patch f v n) f2 (patch g v N) g2 ψ := by
            rw[is_faithful]; constructor; intro w hw
            by_cases h: (w=v : Prop)
            . simp only[patch, h]; dsimp; exact (number_ok n).exists.choose_spec
            . simp only[patch, h]; dsimp
              rw[is_faithful] at faith
              have faith := faith.1 w; simp only[is_free, h] at faith
              dsimp at faith; exact faith hw
            exact faith.2
          exact (ZFC_iff_Lean' _ _ _ _ ψ faith).mpr H
  | .Any2 v ψ =>
    . rw[AriFormula2_to_ZFC', AriFormula2_to_Lean']; constructor
      . intro H; rcases H with ⟨N, ⟨hN, H⟩⟩
        rcases (sub_nat_is_real N hN) with ⟨n, hN⟩; use n
        have faith : is_faithful f (patch f2 v n)  g (patch g2 v N) ψ := by
          rw[is_faithful]; constructor; exact faith.1
          intro w hw
          by_cases h: (w=v : Prop)
          . simp only[patch, h]; dsimp; exact hN.1
          . simp only[patch, h]; dsimp
            rw[is_faithful] at faith
            have faith := faith.2 w; simp only[is_free2, h] at faith
            dsimp at faith; exact faith hw
        exact (ZFC_iff_Lean' _ _ _ _ ψ faith).mp H
      . intro ⟨n, H⟩; set N := (real_ok n).exists.choose; use N
        constructor
        . exact real_is_sub_nat _ _ (real_ok n).exists.choose_spec
        . have faith : is_faithful f (patch f2 v n) g (patch g2 v N) ψ := by
            rw[is_faithful]; constructor; exact faith.1; intro w hw
            by_cases h: (w=v : Prop)
            . simp only[patch, h]; dsimp; exact (real_ok n).exists.choose_spec
            . simp only[patch, h]; dsimp
              rw[is_faithful] at faith
              have faith := faith.2 w; simp only[is_free2, h] at faith
              dsimp at faith; exact faith hw
          exact (ZFC_iff_Lean' _ _ _ _ ψ faith).mpr H
  | .Eq t s =>
    . rw[AriFormula2_to_ZFC', AriFormula2_to_Lean']
      have ft : ∀ (v : ℕ), is_free_t t v → is_number (f v) (g v) := by
        intro v hv; have faith := faith.1 v; rw[is_free] at faith
        exact faith (Or.inl hv)
      have fs : ∀ (v : ℕ), is_free_t s v → is_number (f v) (g v) := by
        intro v hv; have faith := faith.1 v; rw[is_free] at faith
        exact faith (Or.inr hv)
      constructor
      . intro ⟨x, ⟨hxt, hxs⟩ ⟩
        rw[is_term_iff_is_number f g t ft x] at hxt
        rw[is_term_iff_is_number f g s fs x] at hxs
        have ⟨ft, hxt⟩ := finvert (number_card' _ _ hxt)
        have ⟨fs, hxs⟩ := number_card' _ _ hxs
        have : ∃j:(Fin (term_to_nat f t))→(Fin (term_to_nat f s)), Function.Bijective j := by
          use fs∘ft; exact Function.Bijective.comp hxs hxt
        exact fin_bij _ _ this
      . intro ets
        set x := (number_ok (term_to_nat f t)).exists.choose; use x
        rw[is_term_iff_is_number f g t ft x]
        rw[is_term_iff_is_number f g s fs x, ← ets]
        exact ⟨(number_ok _).exists.choose_spec, (number_ok _).exists.choose_spec⟩
  | .Fun fz t =>
    . rw[AriFormula2_to_ZFC', AriFormula2_to_Lean'];
      have U : is_faithful_t2 f2 g2 fz := by
        rw[is_faithful_t2]; intro v; have faith := faith.2 v
        rw[is_free2] at faith; assumption
      have V : is_faithful_t f g t := by
        rw[is_faithful_t]; intro v; have faith := faith.1 v
        rw[is_free] at faith; assumption
      constructor <;> intro H
      . rcases H with ⟨A, ⟨x, ⟨jf, ⟨ht, xA⟩⟩⟩⟩
        rw[is_term2_iff_is_real f2 g2 fz U A] at jf
        rw[is_real] at jf; rcases (jf x).mp xA with ⟨n, ⟨hn, jf⟩⟩
        rw[is_term_iff_is_number f g t V x] at ht
        rw[eqnum _ _ _ ht hn]; assumption
      . set N := term_to_nat f t with Ndef
        set x := (number_ok N).exists.choose
        set F := term2_to_real f2 fz with Fdef
        set A := (real_ok F).exists.choose
        use A; use x; constructor
        . rw[is_term2_iff_is_real f2 g2 fz U A, ← Fdef]
          exact (real_ok F).exists.choose_spec
        constructor
        . rw[is_term_iff_is_number f g t V x, ← Ndef]
          exact (number_ok N).exists.choose_spec
        . exact fL_is_fZ A x N F H (number_ok N).exists.choose_spec (real_ok F).exists.choose_spec

/-- This is the main result: if φ is closed, then φ_C is inhabited iff (φ_Z)_M is inhabited. --/
theorem ZFC_iff_Lean.{u} (φ: AriFormula2) (h: is_sentence φ) :
    (AriFormula2_to_ZFC.{u} φ) ↔ (AriFormula2_to_Lean φ) := by
  rw[AriFormula2_to_Lean, AriFormula2_to_ZFC]; constructor
  . intro H f f2; set g:ℕ→SET.{u} := λ_:ℕ↦NULL.{u}; have H := H g g
    exact (ZFC_iff_Lean'.{u} f f2 g g φ ((sentence_valuation φ h).2.2 f f2 g g)).mp H
  . intro H g g2; set f:ℕ→ℕ := (λ_↦0); set f2:ℕ→Set ℕ := (λ_↦∅); have H := H f f2
    exact (ZFC_iff_Lean'.{u} f f2 g g2 φ ((sentence_valuation φ h).2.2 f f2 g g2)).mpr H
