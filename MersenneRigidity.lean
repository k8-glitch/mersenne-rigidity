import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Positivity

/-!
# メルセンヌ数の相補因子の 2 進剛性定理

Yuto Niwa, “A 2-adic rigidity theorem for complementary divisors of Mersenne numbers”
（2026 年 8 月 26 日の原稿）に基づく。Lean 4 / mathlib v4.25.2。

自然数による主定理は末尾の `mersenne_rigidity`。中間計算では差の符号を
保つため整数を使う。まず深度を挟み込み、二つのディオファントス方程式を
無限降下で処理する。最後に整数の組による倍角公式で数列の 2 冪項を分類する。
-/

set_option maxHeartbeats 1500000

namespace MersenneRigidity

/-- At every level up to p, one congruence implies the other. -/
theorem depth_iff {p k : ℕ} {D E : ℤ}
    (hf : D * E + 1 = 2 ^ p) (hk : k ≤ p) :
    (2 : ℤ) ^ k ∣ D - 1 ↔ (2 : ℤ) ^ k ∣ E + 1 := by
  have hpow : (2 : ℤ) ^ p = 2 ^ k * 2 ^ (p-k) := by
    rw [← pow_add, Nat.add_sub_of_le hk]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨2 ^ (p-k) - a * E, ?_⟩
    linear_combination hf + hpow - E * ha
  · rintro ⟨c, hc⟩
    refine ⟨D * c - 2 ^ (p-k), ?_⟩
    linear_combination D * hc - hf - hpow

private theorem not_square {p : ℕ} (ho : Odd p) :
    ¬ IsSquare ((2 : ℤ) ^ p) := by
  intro hs
  have hcast : IsSquare (((2 : ℕ) ^ p : ℕ) : ℤ) := by simpa using hs
  obtain ⟨a,ha⟩ := Int.isSquare_natCast_iff.mp hcast
  rw [← sq] at ha
  have h := congrArg (fun n : ℕ => n.factorization 2) ha
  change ((2:ℕ)^p).factorization 2 = (a^2).factorization 2 at h
  rw [Nat.factorization_pow_self Nat.prime_two, Nat.factorization_pow] at h
  simp at h
  obtain ⟨b, hb⟩ := ho
  omega

/-- No nontrivial complementary pair at a depth strictly above p/4
    can reach p/3. The supplied t need not be maximal. -/
theorem depth_sandwich {p t : ℕ} {D E : ℤ}
    (hp : Nat.Prime p) (ho : Odd p)
    (hD : 1 < D) (hE : 1 < E) (hf : D * E + 1 = 2 ^ p)
    (hd : (2 : ℤ) ^ t ∣ D - 1) (he : (2 : ℤ) ^ t ∣ E + 1)
    (hdeep : p < 4 * t) : 3 * t < p ∧ p < 4 * t := by
  refine ⟨?_, hdeep⟩
  let x : ℤ := 2 ^ t
  have hx : 1 ≤ x := by
    have h : 0 < x := by dsimp [x]; positivity
    omega
  obtain ⟨A, hA⟩ := hd
  obtain ⟨C, hC⟩ := he
  change D - 1 = x * A at hA
  change E + 1 = x * C at hC
  have ha : 1 ≤ A := by
    by_contra! h
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ x by omega) (show A ≤ 0 by omega)]
  have hc : 1 ≤ C := by
    by_contra! h
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ x by omega) (show C ≤ 0 by omega)]
  have dlo : x + 1 ≤ D := by nlinarith [mul_nonneg (show 0 ≤ x by omega) (sub_nonneg.mpr ha)]
  have elo : x - 1 ≤ E := by nlinarith [mul_nonneg (show 0 ≤ x by omega) (sub_nonneg.mpr hc)]
  have h2 : (2 : ℤ) ^ (2*t) = x*x := by
    simp [x, two_mul, pow_add]
  have h3 : (2 : ℤ) ^ (3*t) = x*x*x := by
    rw [show 3*t = t+t+t by omega, pow_add, pow_add]
  have size2 : (2 : ℤ) ^ (2*t) ≤ 2 ^ p := by
    rw [h2, ← hf]
    nlinarith [mul_le_mul dlo elo (show 0 ≤ x-1 by omega) (show 0 ≤ D by omega)]
  have hexp : 2*t ≤ p := by
    by_contra! h
    exact (not_lt_of_ge size2) (pow_lt_pow_right₀ (by decide : (1 : ℤ) < 2) h)
  let B : ℤ := 2 ^ (p-2*t)
  have split : (2 : ℤ)^p = x*x*B := by
    rw [← h2]; dsimp [B]; rw [← pow_add, Nat.add_sub_of_le hexp]
  have prod : (x*A+1)*(x*C-1)+1 = x*x*B := by
    rw [show x*A+1 = D by omega, show x*C-1 = E by omega, hf, split]
  let j := B-A*C
  have hj : C-A = x*j := by
    apply mul_left_cancel₀ (show x ≠ 0 by omega)
    change x*(C-A) = x*(x*(B-A*C))
    linear_combination prod
  have size3 : x*x*x ≤ D*E+1 := by
    rcases lt_trichotomy j 0 with hn | hz | hpj
    · have hgap : x ≤ A-C := by
        nlinarith [mul_nonneg (show 0 ≤ x by omega) (show 0 ≤ -j-1 by omega)]
      have dbig : x*(x+1)+1 ≤ D := by
        nlinarith [mul_nonneg (show 0 ≤ x by omega) (show 0 ≤ A-(x+1) by omega)]
      nlinarith [mul_le_mul dbig elo (show 0 ≤ x-1 by omega) (show 0 ≤ D by omega)]
    · have hac : C = A := by rw [hz, mul_zero] at hj; omega
      apply False.elim
      apply not_square ho
      refine ⟨x*A, ?_⟩
      rw [← hf, show D = x*A+1 by omega, show E = x*A-1 by rw [hac] at hC; omega]
      ring
    · have hgap : x ≤ C-A := by
        nlinarith [mul_nonneg (show 0 ≤ x by omega) (show 0 ≤ j-1 by omega)]
      have ebig : x*(x+1)-1 ≤ E := by
        nlinarith [mul_nonneg (show 0 ≤ x by omega) (show 0 ≤ C-(x+1) by omega)]
      have hpos : 0 ≤ x*(x+1)-1 := by nlinarith [sq_nonneg x]
      nlinarith [mul_le_mul dlo ebig hpos (show 0 ≤ D by omega), sq_nonneg x]
  rw [← h3, hf] at size3
  have hle : 3*t ≤ p := by
    by_contra! h
    exact (not_lt_of_ge size3) (pow_lt_pow_right₀ (by decide : (1 : ℤ) < 2) h)
  have hne : p ≠ 3*t := by
    intro h
    have hdiv : 3 ∣ p := ⟨t, h⟩
    have hor := hp.eq_one_or_self_of_dvd 3 hdiv
    have hp3 : p = 3 := by omega
    rw [hp3] at hf
    norm_num at hf
    have dsmall : D ≤ 7 := by nlinarith only [hf, mul_nonneg (show 0 ≤ D by omega) (show 0 ≤ E-1 by omega)]
    interval_cases D <;> omega
  omega


/-- Inverse steps of the positive (N) descent. -/
def orbit (y : ℤ) : ℕ → ℤ × ℤ
  | 0 => (1, 1)
  | m+1 => let z := orbit y m; ((y+1)*z.1+z.2, y*z.1+z.2)

private theorem positive_branch_impossible {y q : ℤ} (hy : 2 ≤ y)
    (hey : Even y) (hq : 1 ≤ q)
    (H r a : ℤ) (hr : 1 ≤ r) (hor : Odd r) (ha : 1 ≤ a)
    (s : H = q*r+a) (e : r*r = a*H*y-q) : False := by
  let c := r-a*q*y
  let b := a-q*c
  have ident : c*r = a*a*y-q := by dsimp [c]; rw [s] at e; linear_combination e
  have next : c*c = a*b*y-q := by dsimp [b,c]; rw [s] at e; linear_combination e
  have horc : Odd c := by
    obtain ⟨v,hv⟩ := hey
    obtain ⟨u,hu⟩ := hor
    exact ⟨u-a*q*v, by dsimp [c]; rw [hu,hv]; ring⟩
  have aq : 2 ≤ a*y := by nlinarith [mul_nonneg (sub_nonneg.mpr ha) (show 0 ≤ y by omega)]
  have low : r*r ≥ q*(2*r-1)+2 := by
    rw [s] at e
    nlinarith [mul_nonneg (show 0 ≤ a*y-2 by omega) (show 0 ≤ q*r+a by positivity),
      mul_nonneg (show 0 ≤ q by omega) (show 0 ≤ r by omega)]
  have qr : q < r := by
    by_contra! h
    nlinarith [mul_nonneg (sub_nonneg.mpr h) (show 0 ≤ 2*r-1 by omega),
      mul_nonneg (show 0 ≤ r by omega) (show 0 ≤ r-1 by omega)]
  have hc : 1 ≤ c := by
    by_contra! h
    obtain ⟨k,hk⟩ := horc
    have hn : c ≤ -1 := by omega
    nlinarith [mul_nonneg (show 0 ≤ -c-1 by omega) (show 0 ≤ r by omega),
      mul_nonneg (sq_nonneg a) (show 0 ≤ y by omega)]
  have hb : 1 ≤ b := by
    by_contra! h
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ a*y by omega) (show b ≤ 0 by omega),
      sq_nonneg c]
  have hdown : a < H := by nlinarith [show 0 < q*r by positivity]
  exact positive_branch_impossible hy hey hq a c b hc horc hb
    (by dsimp [b]; ring) (by linear_combination next)
termination_by H.toNat
decreasing_by omega

private theorem negative_branch_orbit {y q : ℤ} (hy : 2 ≤ y) (hq : 1 ≤ q)
    (H r a : ℤ) (hr : 1 ≤ r) (ha : 1 ≤ a)
    (cop : ∃ u v : ℤ, u*a+v*q=1)
    (s : H = q*r+a) (e : r*r = a*H*y+q) :
    q = 1 ∧ ∃ m, orbit y (m+1) = (H,r) := by
  let c := r-a*q*y
  let b := a-q*c
  have ident : c*r = a*a*y+q := by dsimp [c]; rw [s] at e; linear_combination e
  have next : c*c = a*b*y+q := by dsimp [b,c]; rw [s] at e; linear_combination e
  have hc : 1 ≤ c := by
    by_contra! h
    nlinarith [mul_nonpos_of_nonpos_of_nonneg (show c ≤ 0 by omega) (show 0 ≤ r by omega),
      mul_nonneg (sq_nonneg a) (show 0 ≤ y by omega)]
  have ay : 2 ≤ a*y := by nlinarith [mul_nonneg (sub_nonneg.mpr ha) (show 0 ≤ y by omega)]
  have hca : c ≤ a := by
    by_contra! h
    have z : q ≤ c*q-a := by
      nlinarith [mul_nonneg (show 0 ≤ c-a-1 by omega) (show 0 ≤ q by omega),
        mul_nonneg (show 0 ≤ q-1 by omega) (show 0 ≤ a by omega)]
    have z' := mul_le_mul_of_nonneg_left z (show 0 ≤ a*y by omega)
    have heq : q = a*y*(c*q-a)+c*c := by dsimp [c]; rw [s] at e; linear_combination -e
    nlinarith [mul_nonneg (show 0 ≤ a*y-2 by omega) (show 0 ≤ q by omega), sq_nonneg c]
  obtain ⟨u,v,hu⟩ := cop
  by_cases ht : c = a
  · rw [ht] at ident
    have hqform : q = a*(r-a*y) := by nlinarith
    have had : a ∣ 1 := ⟨u+v*(r-a*y), by linear_combination -hu + v*hqform⟩
    have ha1 : a = 1 := by
      have := Int.le_of_dvd (by decide : (0:ℤ)<1) had
      omega
    have hrc : r = a*q*y+c := by dsimp [c]; ring
    rw [ht,ha1] at hrc
    rw [ha1] at hqform
    have hq1 : q = 1 := by
      by_contra! hn
      nlinarith [mul_pos (show 0 < q-1 by omega) (show 0 < y-1 by omega)]
    refine ⟨hq1, 0, ?_⟩
    simp only [orbit]
    apply Prod.ext <;> simp <;> rw [hq1,ha1] at s <;> rw [hq1] at hrc <;> linarith
  · have hb : 1 ≤ b := by
      by_contra! hn
      by_cases hz : b = 0
      · have aq : a = q*c := by change a-q*c=0 at hz; omega
        have hqd : q ∣ 1 := ⟨u*c+v, by rw [aq] at hu; linear_combination -hu⟩
        have := Int.le_of_dvd (by decide : (0:ℤ)<1) hqd
        have q1 : q = 1 := by omega
        rw [q1] at aq
        omega
      · have hab : a-b = q*c := by dsimp [b]; ring
        have prod : q*c-1 ≤ a*(-b) := by
          nlinarith [mul_nonneg (show 0 ≤ a-1 by omega) (show 0 ≤ -b-1 by omega)]
        have z := mul_le_mul_of_nonneg_left prod (show 0 ≤ y by omega)
        have qc : q ≤ q*c := by nlinarith [mul_nonneg (show 0 ≤ q by omega) (show 0 ≤ c-1 by omega)]
        have hcc : 1 ≤ c*c := by nlinarith [sq_nonneg (c-1)]
        have ltq : c*c < q := by nlinarith [mul_pos (show 0 < a*y by omega) (show 0 < -b by omega)]
        nlinarith [mul_nonneg (show 0 ≤ y-2 by omega) (show 0 ≤ q*c-1 by omega)]
    have cop' : ∃ U V : ℤ, U*b+V*q=1 := ⟨u,v+u*c,by dsimp [b]; linear_combination hu⟩
    have hdown : a < H := by nlinarith [show 0 < q*r by positivity]
    obtain ⟨q1,m,hm⟩ := negative_branch_orbit hy hq a c b hc hb cop'
      (by dsimp [b]; ring) (by linear_combination next)
    refine ⟨q1,m+1,?_⟩
    rw [orbit, hm]
    apply Prod.ext <;> dsimp [c] <;> rw [q1] at s ⊢ <;> nlinarith
termination_by H.toNat
decreasing_by omega

/-- Coefficients of (z + √(z²-1))^k, computed over the integers. -/
private def pell (z : ℤ) : ℕ → ℤ × ℤ
  | 0 => (1,0)
  | k+1 => let b := pell z k; (z*b.1+(z*z-1)*b.2, b.1+z*b.2)

private theorem pell_add (z : ℤ) (i j : ℕ) :
    pell z (i+j) =
      ((pell z i).1*(pell z j).1+(z*z-1)*(pell z i).2*(pell z j).2,
       (pell z i).1*(pell z j).2+(pell z i).2*(pell z j).1) := by
  induction j with
  | zero => simp [pell]
  | succ j ih =>
    rw [Nat.add_succ]
    simp only [pell, ih]
    apply Prod.ext <;> dsimp <;> ring

private theorem orbit_pell (z : ℤ) (m : ℕ) :
    orbit (2*z-2) m =
      ((pell z (m+1)).2,(pell z (m+1)).2-(pell z m).2) := by
  induction m with
  | zero => simp [pell,orbit]
  | succ m ih =>
    simp only [orbit,ih,pell]
    apply Prod.ext <;> dsimp <;> ring

private theorem pell_bounds {z : ℤ} (hz : 2 ≤ z) (k : ℕ) :
    (k:ℤ)+1 ≤ (pell z k).1 ∧ 0 ≤ (pell z k).2 := by
  induction k with
  | zero => simp [pell]
  | succ k ih =>
    obtain ⟨hv,hu⟩ := ih
    have hv0 : 1 ≤ (pell z k).1 := by omega
    have hz2 : 0 ≤ z*z-1 := by nlinarith [sq_nonneg (z-1)]
    simp only [pell, Nat.cast_succ]
    constructor
    · nlinarith [mul_nonneg (show 0 ≤ z-2 by omega) (show 0 ≤ (pell z k).1 by omega),
        mul_nonneg hz2 hu]
    · nlinarith [mul_nonneg (show 0 ≤ z by omega) hu]

private theorem pell_parity (z : ℤ) (k : ℕ) :
    (pell z k).2 % 2 = (k:ℤ) % 2 ∧
      (pell z (k+1)).2 % 2 = ((k:ℤ)+1) % 2 := by
  induction k with
  | zero => simp [pell]
  | succ k ih =>
    refine ⟨by simpa using ih.2, ?_⟩
    have h : (pell z (k+2)).2 = 2*(z*(pell z (k+1)).2)-(pell z k).2 := by
      simp [pell]; ring
    rw [show k+1+1 = k+2 by omega, h]
    push_cast
    omega

private theorem pell_v_odd {z : ℤ} (hz : Odd z) (k : ℕ) :
    Odd (pell z k).1 := by
  obtain ⟨w,hw⟩ := hz
  induction k with
  | zero => exact ⟨0,by simp [pell]⟩
  | succ k ih =>
    obtain ⟨v,hv⟩ := ih
    refine ⟨w*(pell z k).1+v+(2*w*w+2*w)*(pell z k).2, ?_⟩
    simp only [pell]
    linear_combination (pell z k).1*hw + hv +
      (z + (2*w+1))*(pell z k).2*hw

private theorem pell_v_mod4 (k : ℕ) :
    (pell 2 k).1 % 4 ≠ 0 ∧ (pell 2 (k+1)).1 % 4 ≠ 0 := by
  induction k with
  | zero => decide
  | succ k ih =>
    refine ⟨ih.2,?_⟩
    have h : (pell 2 (k+2)).1 = 4*(pell 2 (k+1)).1-(pell 2 k).1 := by
      simp [pell]; ring
    rw [show k+1+1 = k+2 by omega,h]
    omega

private theorem divisor_pow_two {v : ℤ} (hv : 0 ≤ v) {n : ℕ}
    (hd : v ∣ (2:ℤ)^n) : ∃ b : ℕ, v = 2^b := by
  lift v to ℕ using hv
  have hn : v ∣ (2:ℕ)^n := by exact_mod_cast hd
  obtain ⟨b,_,hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hn
  exact ⟨b,by exact_mod_cast hb⟩

private theorem orbit_classification {i j m : ℕ} (hi : 0 < i) (hj : 0 < j)
    (heq : (orbit ((2:ℤ)^j) m).1 = 2^i) :
    (2:ℤ)^j = 2 ∧ m = 1 := by
  obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  let z : ℤ := 2^l+1
  have hz : 2 ≤ z := by
    have : (0:ℤ) < 2^l := by positivity
    dsimp [z]; omega
  have hy : (2:ℤ)^(l+1) = 2*z-2 := by dsimp [z]; rw [pow_succ]; ring
  rw [hy,orbit_pell] at heq
  change (pell z (m+1)).2 = 2^i at heq
  obtain ⟨i',rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  have hpar := (pell_parity z (m+1)).1
  rw [heq,pow_succ] at hpar
  push_cast at hpar
  let k := (m+1)/2
  have hmk : m+1 = k+k := by dsimp [k]; omega
  have hu := congrArg Prod.snd (pell_add z k k)
  change (pell z (k+k)).2 = _ at hu
  have hdiv : (pell z k).1 ∣ (2:ℤ)^(i'+1) := by
    refine ⟨2*(pell z k).2,?_⟩
    rw [← heq,hmk,hu]; dsimp; ring
  have hb := (pell_bounds hz k).1
  have hkp : 0 < k := by omega
  obtain ⟨b,hbpow⟩ := divisor_pow_two (by omega) hdiv
  have bpos : b ≠ 0 := by intro e; rw [e,pow_zero] at hbpow; omega
  obtain ⟨b',rfl⟩ := Nat.exists_eq_succ_of_ne_zero bpos
  have hl : l = 0 := by
    by_contra! hn
    obtain ⟨l',hl'⟩ := Nat.exists_eq_succ_of_ne_zero hn
    have hzodd : Odd z := ⟨2^l',by dsimp [z]; rw [hl',pow_succ]; ring⟩
    obtain ⟨v,hv⟩ := pell_v_odd hzodd k
    rw [pow_succ] at hbpow
    omega
  have hz2 : z = 2 := by simp [z,hl]
  rw [hz2] at hbpow hb
  have hb0 : b' = 0 := by
    by_contra! hn
    obtain ⟨b'',he⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [he,pow_succ,pow_succ] at hbpow
    have := (pell_v_mod4 k).1
    omega
  rw [hb0] at hbpow
  norm_num at hbpow
  exact ⟨by simp [hl],by omega⟩

private theorem pow_two_even {n : ℕ} (hn : 0 < n) : Even ((2:ℤ)^n) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  exact ⟨2^k,by rw [pow_succ]; ring⟩

private theorem normalized {i l : ℕ} (hi : 0 < i) (hl : 0 < l)
    {x H y A C j : ℤ} (hH : H=2^i) (hy : y=2^l) (hx : x=H*y)
    (hA : 1 ≤ A) (hC : 1 ≤ C) (oA : Odd A) (oC : Odd C)
    (hdif : C-A=x*j) (hs : A*C+j=x*H) :
    x=8 ∧ H=4 ∧ A=11 ∧ C=3 := by
  have eH : Even H := hH ▸ pow_two_even hi
  have ey : Even y := hy ▸ pow_two_even hl
  have ex : Even x := hx ▸ eH.mul_right _
  obtain ⟨w,hw⟩ := ex
  have Hpos : 0 < H := by rw [hH]; positivity
  have ypos : 0 < y := by rw [hy]; positivity
  obtain ⟨v,hv⟩ := eH
  obtain ⟨u,hu⟩ := ey
  have H2 : 2 ≤ H := by omega
  have y2 : 2 ≤ y := by omega
  have x2 : 2*H ≤ x := by nlinarith only [hx,mul_nonneg Hpos.le (sub_nonneg.mpr y2)]
  have xp : 2 ≤ x := by omega
  rcases lt_trichotomy j 0 with hn | hz | hpj
  · let q := -j
    let a := H-q*C
    have qp : 1 ≤ q := by dsimp [q]; omega
    have eqN : C*C = a*x+q := by
      dsimp [a,q]; linear_combination hs + C*hdif
    have eqH : H=q*C+a := by dsimp [a]; ring
    have oq : Odd q := by
      obtain ⟨k,hk⟩ := oC.mul oC
      exact ⟨k-a*w,by linear_combination hk - eqN - a*hw⟩
    have qsmall : q < x := by
      by_contra! h
      have z : x-1 ≤ x*C-1 := by nlinarith only [mul_nonneg (show 0 ≤ x by omega) (sub_nonneg.mpr hC)]
      have eq : x*H=C*C+q*(x*C-1) := by dsimp [q]; linear_combination -hs - C*hdif
      nlinarith only [eq, mul_le_mul h z (show 0 ≤ x-1 by omega) (show 0 ≤ q by omega),
        mul_nonneg (show 0 ≤ x by omega) (show 0 ≤ x-H-1 by omega),
        show 0 < C*C by positivity]
    have ap : 1 ≤ a := by
      by_contra! h
      by_cases az : a=0
      · obtain ⟨k,hk⟩ := oq.mul oC
        rw [az] at eqH
        omega
      · nlinarith only [eqN, qsmall,sq_nonneg C,
          mul_nonneg (show 0 ≤ -a-1 by omega) (show 0 ≤ x by omega)]
    obtain ⟨z,hz⟩ := oq
    have cop2 : IsCoprime q 2 := ⟨1,-z,by linarith⟩
    have copH : IsCoprime q H := by rw [hH]; exact cop2.pow_right
    obtain ⟨f,g,hfg⟩ := copH
    have cop : ∃ U V : ℤ, U*a+V*q=1 :=
      ⟨g,f+g*C,by linear_combination hfg - g*eqH⟩
    have en : C*C=a*H*y+q := by rw [eqN,hx]; ring
    obtain ⟨q1,m,hm⟩ := negative_branch_orbit y2 qp H C a hC ap cop eqH en
    have heq : (orbit ((2:ℤ)^l) (m+1)).1 = 2^i := by rw [← hy,hm]; exact hH
    obtain ⟨hy2,hm1⟩ := orbit_classification hi hl heq
    have yy : y=2 := hy.trans hy2
    rw [yy,hm1] at hm
    norm_num [orbit] at hm
    have HH : H=4 := by omega
    have CC : C=3 := by omega
    have xx : x=8 := by rw [hx,HH,yy]; norm_num
    have jj : j = -1 := by change -j=1 at q1; omega
    rw [xx,CC,jj] at hdif
    exact ⟨xx,HH,by omega,CC⟩
  · rw [hz, mul_zero] at hdif
    have ca : C=A := by omega
    obtain ⟨k,hk⟩ := oA.mul oA
    rw [hz,ca,add_zero] at hs
    have zz : A*A = 2*(w*H) := by rw [hs,hw]; ring
    omega
  · let a := H-j*A
    have e : A*A=a*x-j := by dsimp [a]; linear_combination hs - A*hdif
    have ap : 1 ≤ a := by
      by_contra! h
      nlinarith only [e,sq_nonneg A,hpj,mul_nonpos_of_nonpos_of_nonneg (show a ≤ 0 by omega) (show 0 ≤ x by omega)]
    have ep : A*A=a*H*y-j := by rw [e,hx]; ring
    exact False.elim (positive_branch_impossible y2 ⟨u,hu⟩ (by omega : 1 ≤ j)
      H A a hA oA ap (by dsimp [a]; ring) ep)

/-- Rigidity of a deep complementary divisor pair (Niwa, August 2026). -/
theorem rigidity {p : ℕ} (hp : Nat.Prime p) (ho : Odd p) {D E : ℤ}
    (hD : 1 < D) (hE : 1 < E) (hf : D*E+1 = 2^p)
    (t : ℕ) (hdeep : p < 4*t)
    (hd : (2:ℤ)^t ∣ D-1) (he : (2:ℤ)^t ∣ E+1) :
    p=11 ∧ D=89 ∧ E=23 := by
  obtain ⟨lower,upper⟩ := depth_sandwich hp ho hD hE hf hd he hdeep
  let x : ℤ := 2^t
  let H : ℤ := 2^(p-3*t)
  let y : ℤ := 2^(4*t-p)
  have xp : 0 < x := by dsimp [x]; positivity
  have hx : x=H*y := by dsimp [x,H,y]; rw [← pow_add]; congr 1; omega
  have hpow : (2:ℤ)^p = x*x*x*H := by
    dsimp [x,H]; rw [← pow_add,← pow_add,← pow_add]; congr 1; omega
  obtain ⟨A,ha⟩ := hd
  obtain ⟨C,hc⟩ := he
  change D-1=x*A at ha
  change E+1=x*C at hc
  have hA : 1 ≤ A := by
    by_contra! h
    nlinarith only [ha,hD,mul_nonpos_of_nonneg_of_nonpos xp.le (show A ≤ 0 by omega)]
  have hC : 1 ≤ C := by
    by_contra! h
    nlinarith only [hc,hE,mul_nonpos_of_nonneg_of_nonpos xp.le (show C ≤ 0 by omega)]
  by_cases eA : Even A
  · obtain ⟨k,hk⟩ := eA
    have hd' : (2:ℤ)^(t+1) ∣ D-1 := ⟨k,by rw [pow_succ]; change D-1=x*2*k; rw [ha,hk]; ring⟩
    have he' := (depth_iff hf (by omega : t+1 ≤ p)).mp hd'
    exact rigidity hp ho hD hE hf (t+1) (by omega) hd' he'
  · have oA : Odd A := Int.not_even_iff_odd.mp eA
    let j := x*H-A*C
    have hs : A*C+j=x*H := by dsimp [j]; ring
    have hdif : C-A=x*j := by
      apply mul_left_cancel₀ (ne_of_gt xp)
      have prod : (x*A+1)*(x*C-1)+1=x*x*x*H := by
        rw [show x*A+1=D by omega,show x*C-1=E by omega,hf,hpow]
      dsimp [j]; linear_combination prod
    obtain ⟨w,hw⟩ := pow_two_even (by omega : 0 < t)
    change x = w+w at hw
    obtain ⟨k,hk⟩ := oA
    have oC : Odd C := ⟨k+w*j,by linear_combination hdif + hk + j*hw⟩
    obtain ⟨xx,HH,AA,CC⟩ := normalized (i:=p-3*t) (l:=4*t-p) (by omega)
      (by omega) (show H=_ from rfl) (show y=_ from rfl) hx hA hC ⟨k,hk⟩ oC hdif hs
    have tinj := (pow_right_strictMono₀ (by decide : (1:ℤ)<2)).injective
    have tt : t=3 := tinj (show (2:ℤ)^t=2^3 from xx)
    have hh : p-3*t=2 := tinj (show (2:ℤ)^(p-3*t)=2^2 from HH)
    rw [xx,AA] at ha
    rw [xx,CC] at hc
    exact ⟨by omega,by omega,by omega⟩
termination_by p-t
decreasing_by omega

/-- The exceptional factorization satisfies the hypotheses with depth three. -/
theorem exceptional_example :
    (89:ℤ)*23+1=2^11 ∧ (2:ℤ)^3 ∣ 89-1 ∧ (2:ℤ)^3 ∣ 23+1 ∧ 11<4*3 := by decide

/-- The manuscript's main theorem with all four variables in the natural numbers. -/
theorem mersenne_rigidity {p D E t : ℕ} (hp : Nat.Prime p) (ho : Odd p)
    (hD : 1 < D) (hE : 1 < E) (hf : 2^p-1 = D*E)
    (ht : p < 4*t) (hd : 2^t ∣ D-1) (he : 2^t ∣ E+1) :
    p=11 ∧ D=89 ∧ E=23 := by
  have hpos : 0 < (2:ℕ)^p := by positivity
  have hf' : D*E+1 = 2^p := by omega
  have hd' : (2:ℤ)^t ∣ (D:ℤ)-1 := by
    have hh : (((2:ℕ)^t : ℕ) : ℤ) ∣ ((D-1 : ℕ) : ℤ) := by exact_mod_cast hd
    simpa [Nat.cast_sub (by omega : 1 ≤ D)] using hh
  obtain ⟨pp,dd,ee⟩ := rigidity hp ho (D:=(D:ℤ)) (E:=(E:ℤ))
    (by exact_mod_cast hD) (by exact_mod_cast hE) (by exact_mod_cast hf')
    t ht hd' (by exact_mod_cast he)
  exact ⟨pp,by exact_mod_cast dd,by exact_mod_cast ee⟩

#print axioms mersenne_rigidity
end MersenneRigidity
