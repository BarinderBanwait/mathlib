/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import group_theory.group_action group_theory.quotient_group
import group_theory.order_of_element data.zmod.basic ring_theory.multiplicity

open equiv fintype finset mul_action function
open equiv.perm is_subgroup list quotient_group
universes u v w
variables {G : Type u} {α : Type v} {β : Type w} [group G]

local attribute [instance, priority 0] subtype.fintype set_fintype classical.prop_decidable

namespace mul_action
variables [mul_action G α]

lemma mem_fixed_points_iff_card_orbit_eq_one {a : α}
  [fintype (orbit G a)] : a ∈ fixed_points G α ↔ card (orbit G a) = 1 :=
begin
  rw [fintype.card_eq_one_iff, mem_fixed_points],
  split,
  { exact λ h, ⟨⟨a, mem_orbit_self _⟩, λ ⟨b, ⟨x, hx⟩⟩, subtype.eq $ by simp [h x, hx.symm]⟩ },
  { assume h x,
    rcases h with ⟨⟨z, hz⟩, hz₁⟩,
    exact calc x • a = z : subtype.mk.inj (hz₁ ⟨x • a, mem_orbit _ _⟩)
      ... = a : (subtype.mk.inj (hz₁ ⟨a, mem_orbit_self _⟩)).symm }
end

lemma card_modeq_card_fixed_points [fintype α] [fintype G] [fintype (fixed_points G α)]
  {p n : ℕ} (hp : nat.prime p) (h : card G = p ^ n) : card α ≡ card (fixed_points G α) [MOD p] :=
calc card α = card (Σ y : quotient (orbit_rel G α), {x // quotient.mk' x = y}) :
  card_congr (equiv_fib (@quotient.mk' _ (orbit_rel G α)))
... = univ.sum (λ a : quotient (orbit_rel G α), card {x // quotient.mk' x = a}) : card_sigma _
... ≡ (@univ (fixed_points G α) _).sum (λ _, 1) [MOD p] :
begin
  rw [← zmodp.eq_iff_modeq_nat hp, sum_nat_cast, sum_nat_cast],
  refine eq.symm (sum_bij_ne_zero (λ a _ _, quotient.mk' a.1)
    (λ _ _ _, mem_univ _)
    (λ a₁ a₂ _ _ _ _ h,
      subtype.eq ((mem_fixed_points' α).1 a₂.2 a₁.1 (quotient.exact' h)))
      (λ b, _)
      (λ a ha _, by rw [← mem_fixed_points_iff_card_orbit_eq_one.1 a.2];
        simp only [quotient.eq']; congr)),
  { refine quotient.induction_on' b (λ b _ hb, _),
    have : card (orbit G b) ∣ p ^ n,
    { rw [← h, fintype.card_congr (orbit_equiv_quotient_stabilizer G b)];
      exact card_quotient_dvd_card _ },
    rcases (nat.dvd_prime_pow hp).1 this with ⟨k, _, hk⟩,
    have hb' :¬ p ^ 1 ∣ p ^ k,
    { rw [nat.pow_one, ← hk, ← nat.modeq.modeq_zero_iff, ← zmodp.eq_iff_modeq_nat hp,
        nat.cast_zero, ← ne.def],
      exact eq.mpr (by simp only [quotient.eq']; congr) hb },
    have : k = 0 := nat.le_zero_iff.1 (nat.le_of_lt_succ (lt_of_not_ge (mt (nat.pow_dvd_pow p) hb'))),
    refine ⟨⟨b, mem_fixed_points_iff_card_orbit_eq_one.2 $ by rw [hk, this, nat.pow_zero]⟩, mem_univ _,
      by simp [zero_ne_one], rfl⟩ }
end
... = _ : by simp; refl

end mul_action

lemma quotient_group.card_preimage_mk [fintype G] (s : set G) [is_subgroup s]
  (t : set (quotient s)) : fintype.card (quotient_group.mk ⁻¹' t) =
  fintype.card s * fintype.card t :=
by rw [← fintype.card_prod, fintype.card_congr
  (preimage_mk_equiv_subgroup_times_set _ _)]

namespace sylow

def mk_vector_prod_eq_one (n : ℕ) (v : vector G n) : vector G (n+1) :=
v.to_list.prod⁻¹ :: v

lemma mk_vector_prod_eq_one_inj (n : ℕ) : injective (@mk_vector_prod_eq_one G _ n) :=
λ ⟨v, _⟩ ⟨w, _⟩ h, subtype.eq (show v = w, by injection h with h; injection h)

def vectors_prod_eq_one (G : Type*) [group G] (n : ℕ) : set (vector G n) :=
{v | v.to_list.prod = 1}

lemma mem_vectors_prod_eq_one {n : ℕ} (v : vector G n) :
  v ∈ vectors_prod_eq_one G n ↔ v.to_list.prod = 1 := iff.rfl

lemma mem_vectors_prod_eq_one_iff {n : ℕ} (v : vector G (n + 1)) :
  v ∈ vectors_prod_eq_one G (n + 1) ↔ v ∈ set.range (@mk_vector_prod_eq_one G _ n) :=
⟨λ (h : v.to_list.prod = 1), ⟨v.tail,
  begin
    unfold mk_vector_prod_eq_one,
    conv {to_rhs, rw ← vector.cons_head_tail v},
    suffices : (v.tail.to_list.prod)⁻¹ = v.head,
    { rw this },
    rw [← mul_right_inj v.tail.to_list.prod, inv_mul_self, ← list.prod_cons,
      ← vector.to_list_cons, vector.cons_head_tail, h]
  end⟩,
  λ ⟨w, hw⟩, by rw [mem_vectors_prod_eq_one, ← hw, mk_vector_prod_eq_one,
    vector.to_list_cons, list.prod_cons, inv_mul_self]⟩

def rotate_vectors_prod_eq_one (G : Type*) [group G] (n : ℕ+) (m : multiplicative (zmod n))
  (v : vectors_prod_eq_one G n) : vectors_prod_eq_one G n :=
⟨⟨v.1.to_list.rotate m.1, by simp⟩, prod_rotate_eq_one_of_prod_eq_one v.2 _⟩

instance rotate_vectors_prod_eq_one.mul_action (n : ℕ+) :
  mul_action (multiplicative (zmod n)) (vectors_prod_eq_one G n) :=
{ smul := (rotate_vectors_prod_eq_one G n),
  one_smul := λ v, subtype.eq $ vector.eq _ _ $ rotate_zero v.1.to_list,
  mul_smul := λ a b ⟨⟨v, hv₁⟩, hv₂⟩, subtype.eq $ vector.eq _ _ $
    show v.rotate ((a + b : zmod n).val) = list.rotate (list.rotate v (b.val)) (a.val),
    by rw [zmod.add_val, rotate_rotate, ← rotate_mod _ (b.1 + a.1), add_comm, hv₁] }

lemma one_mem_vectors_prod_eq_one (n : ℕ) : vector.repeat (1 : G) n ∈ vectors_prod_eq_one G n :=
by simp [vector.repeat, vectors_prod_eq_one]

lemma one_mem_fixed_points_rotate (n : ℕ+) :
  (⟨vector.repeat (1 : G) n, one_mem_vectors_prod_eq_one n⟩ : vectors_prod_eq_one G n) ∈
  fixed_points (multiplicative (zmod n)) (vectors_prod_eq_one G n) :=
λ m, subtype.eq $ vector.eq _ _ $
by haveI : nonempty G := ⟨1⟩; exact
rotate_eq_self_iff_eq_repeat.2 ⟨(1 : G),
  show list.repeat (1 : G) n = list.repeat 1 (list.repeat (1 : G) n).length, by simp⟩ _

/-- Cauchy's theorem -/
lemma exists_prime_order_of_dvd_card [fintype G] {p : ℕ} (hp : nat.prime p)
  (hdvd : p ∣ card G) : ∃ x : G, order_of x = p :=
let n : ℕ+ := ⟨p - 1, nat.sub_pos_of_lt hp.gt_one⟩ in
let p' : ℕ+ := ⟨p, hp.pos⟩ in
have hn : p' = n + 1 := subtype.eq (nat.succ_sub hp.pos),
have hcard : card (vectors_prod_eq_one G (n + 1)) = card G ^ (n : ℕ),
  by rw [set.ext mem_vectors_prod_eq_one_iff,
    set.card_range_of_injective (mk_vector_prod_eq_one_inj _), card_vector],
have hzmod : fintype.card (multiplicative (zmod p')) =
  (p' : ℕ) ^ 1 := (nat.pow_one p').symm ▸ card_fin _,
have hmodeq : _ = _ := @mul_action.card_modeq_card_fixed_points
  (multiplicative (zmod p')) (vectors_prod_eq_one G p') _ _ _ _ _ _ 1 hp hzmod,
have hdvdcard : p ∣ fintype.card (vectors_prod_eq_one G (n + 1)) :=
  calc p ∣ card G ^ 1 : by rwa nat.pow_one
  ... ∣ card G ^ (n : ℕ) : nat.pow_dvd_pow _ n.2
  ... = card (vectors_prod_eq_one G (n + 1)) : hcard.symm,
have hdvdcard₂ : p ∣ card (fixed_points (multiplicative (zmod p')) (vectors_prod_eq_one G p')) :=
  nat.dvd_of_mod_eq_zero (hmodeq ▸ hn.symm ▸ nat.mod_eq_zero_of_dvd hdvdcard),
have hcard_pos : 0 < card (fixed_points (multiplicative (zmod p')) (vectors_prod_eq_one G p')) :=
  fintype.card_pos_iff.2 ⟨⟨⟨vector.repeat 1 p', one_mem_vectors_prod_eq_one _⟩,
    one_mem_fixed_points_rotate _⟩⟩,
have hlt : 1 < card (fixed_points (multiplicative (zmod p')) (vectors_prod_eq_one G p')) :=
  calc (1 : ℕ) < p' : hp.gt_one
  ... ≤ _ : nat.le_of_dvd hcard_pos hdvdcard₂,
let ⟨⟨⟨⟨x, hx₁⟩, hx₂⟩, hx₃⟩, hx₄⟩ := fintype.exists_ne_of_card_gt_one hlt
  ⟨_, one_mem_fixed_points_rotate p'⟩ in
have hx : x ≠ list.repeat (1 : G) p', from λ h, by simpa [h, vector.repeat] using hx₄,
have nG : nonempty G, from ⟨1⟩,
have ∃ a, x = list.repeat a x.length := by exactI rotate_eq_self_iff_eq_repeat.1 (λ n,
  have list.rotate x (n : zmod p').val = x :=
    subtype.mk.inj (subtype.mk.inj (hx₃ (n : zmod p'))),
  by rwa [zmod.val_cast_nat, ← hx₁, rotate_mod] at this),
let ⟨a, ha⟩ := this in
⟨a, have hx1 : x.prod = 1 := hx₂,
  have ha1: a ≠ 1, from λ h, hx (ha.symm ▸ h ▸ hx₁ ▸ rfl),
  have a ^ p = 1, by rwa [ha, list.prod_repeat, hx₁] at hx1,
  (hp.2 _ (order_of_dvd_of_pow_eq_one this)).resolve_left
    (λ h, ha1 (order_of_eq_one_iff.1 h))⟩

open is_subgroup is_submonoid is_group_hom mul_action

lemma mem_fixed_points_mul_left_cosets_iff_mem_normalizer {H : set G} [is_subgroup H] [fintype H]
  {x : G} : (x : quotient H) ∈ fixed_points H (quotient H) ↔ x ∈ normalizer H :=
⟨λ hx, have ha : ∀ {y : quotient H}, y ∈ orbit H (x : quotient H) → y = x,
  from λ _, ((mem_fixed_points' _).1 hx _),
  (inv_mem_iff _).1 (mem_normalizer_fintype (λ n hn,
    have (n⁻¹ * x)⁻¹ * x ∈ H := quotient_group.eq.1 (ha (mem_orbit _ ⟨n⁻¹, inv_mem hn⟩)),
    by simpa only [mul_inv_rev, inv_inv] using this)),
λ (hx : ∀ (n : G), n ∈ H ↔ x * n * x⁻¹ ∈ H),
(mem_fixed_points' _).2 $ λ y, quotient.induction_on' y $ λ y hy, quotient_group.eq.2
  (let ⟨⟨b, hb₁⟩, hb₂⟩ := hy in
  have hb₂ : (b * x)⁻¹ * y ∈ H := quotient_group.eq.1 hb₂,
  (inv_mem_iff H).1 $ (hx _).2 $ (mul_mem_cancel_right H (inv_mem hb₁)).1
  $ by rw hx at hb₂;
    simpa [mul_inv_rev, mul_assoc] using hb₂)⟩

lemma fixed_points_mul_left_cosets_equiv_quotient (H : set G) [is_subgroup H] [fintype H] :
  fixed_points H (quotient H) ≃ quotient (subtype.val ⁻¹' H : set (normalizer H)) :=
@subtype_quotient_equiv_quotient_subtype G (normalizer H) (id _) (id _) (fixed_points _ _)
  (λ a, mem_fixed_points_mul_left_cosets_iff_mem_normalizer.symm) (by intros; refl)

local attribute [instance] set_fintype

lemma exists_subgroup_card_pow_prime [fintype G] {p : ℕ} : ∀ {n : ℕ} (hp : nat.prime p)
  (hdvd : p ^ n ∣ card G), ∃ H : set G, is_subgroup H ∧ fintype.card H = p ^ n
| 0 := λ _ _, ⟨trivial G, by apply_instance, by simp⟩
| (n+1) := λ hp hdvd,
let ⟨H, ⟨hH1, hH2⟩⟩ := exists_subgroup_card_pow_prime hp
  (dvd.trans (nat.pow_dvd_pow _ (nat.le_succ _)) hdvd) in
let ⟨s, hs⟩ := exists_eq_mul_left_of_dvd hdvd in
by exactI
have hcard : card (quotient H) = s * p :=
  (nat.mul_right_inj (show card H > 0, from fintype.card_pos_iff.2
      ⟨⟨1, is_submonoid.one_mem H⟩⟩)).1
    (by rwa [← card_eq_card_quotient_mul_card_subgroup, hH2, hs,
      nat.pow_succ, mul_assoc, mul_comm p]),
have hm : s * p % p = card (quotient (subtype.val ⁻¹' H : set (normalizer H))) % p :=
  card_congr (fixed_points_mul_left_cosets_equiv_quotient H) ▸ hcard ▸
    card_modeq_card_fixed_points hp hH2,
have hm' : p ∣ card (quotient (subtype.val ⁻¹' H : set (normalizer H))) :=
  nat.dvd_of_mod_eq_zero
    (by rwa [nat.mod_eq_zero_of_dvd (dvd_mul_left _ _), eq_comm] at hm),
let ⟨x, hx⟩ := @exists_prime_order_of_dvd_card _ (quotient_group.group _) _ _ hp hm' in
have hxcard : ∀ {f : fintype (gpowers x)}, card (gpowers x) = p,
  from λ f, by rw [← hx, order_eq_card_gpowers]; congr,
have is_subgroup (mk ⁻¹' gpowers x),
  from is_group_hom.preimage _ _,
have fintype (mk ⁻¹' gpowers x), by apply_instance,
have hequiv : H ≃ (subtype.val ⁻¹' H : set (normalizer H)) :=
  equiv.set.preimage _ _,
⟨subtype.val '' (mk ⁻¹' gpowers x), by apply_instance,
  by rw [set.card_image_of_injective (mk ⁻¹' gpowers x) subtype.val_injective,
      nat.pow_succ, ← hH2, fintype.card_congr hequiv, ← hx, order_eq_card_gpowers,
      ← fintype.card_prod];
    exact @fintype.card_congr _ _ (id _) (id _) (preimage_mk_equiv_subgroup_times_set _ _)⟩

end sylow

lemma multiplicity_card_finite [fintype G] {p : ℕ} (hp : p.prime) : 
  multiplicity.finite p (card G) :=
multiplicity.finite_nat_iff.2 ⟨hp.ne_one, fintype.card_pos_iff.2 ⟨1⟩⟩

class is_sylow [fintype G] (H : set G) {p : ℕ} (hp : p.prime) extends is_subgroup H : Prop := 
(card_eq : card H = p ^ (multiplicity p (card G)).get (multiplicity_card_finite hp))

def sylow_subgroup (G : Type u) [group G] [fintype G] {p : ℕ} (hp : p.prime) : Type u :=
{ s : set G // is_sylow s hp }

instance [fintype G] {p : ℕ} (hp : p.prime) :
  has_coe (sylow_subgroup G hp) (set G) := ⟨subtype.val⟩

instance sylow_subgroup.is_subgroup [fintype G] {p : ℕ} (hp : p.prime) 
  (H : sylow_subgroup G hp) : is_subgroup (H : set G) := H.2.to_is_subgroup

instance sylow_subgroup.is_sylow [fintype G] {p : ℕ} (hp : p.prime) 
  (H : sylow_subgroup G hp) : is_sylow (H : set G) hp := H.2

noncomputable instance sylow_subgroup.fintype [fintype G] {p : ℕ} (hp : p.prime) :
  fintype (sylow_subgroup G hp) := subtype.fintype _

instance [fintype G] {p : ℕ} (hp : p.prime) : has_scalar G (sylow_subgroup G hp) :=
{ smul := λ g s, ⟨group.conjugates_of_set s, 
  _, 
  _⟩ }


instance [fintype G] {p : ℕ} (hp : p.prime) : mul_action G (sylow_subgroup G hp) :=
{ to_has_scalar := ⟨begin end⟩ }

def conjugate_set (x : G) (H : set G) : set G :=
(λ n, x⁻¹ * n * x) ⁻¹' H

lemma conjugate_set_eq_image (H : set G) (x : G) :
  conjugate_set x H = (λ n, x * n * x⁻¹) '' H :=
eq.symm (congr_fun (set.image_eq_preimage_of_inverse 
  (λ _, by simp [mul_assoc]) (λ _, by simp [mul_assoc])) _)

lemma conjugate_set_eq_preimage (H : set G) (x : G) :
  conjugate_set x H = (λ n, x⁻¹ * n * x) ⁻¹' H := rfl

instance conjugate_set.is_group_action : is_group_action (@conjugate_set G _) :=
{ one := λ H, by simp [conjugate_set_eq_image, set.image],
  mul := λ x y H, by simp [mul_inv_rev, mul_assoc, comp, conjugate_set_eq_preimage,
    set.preimage] }

@[simp] lemma conjugate_set_normal_subgroup (H : set G) [normal_subgroup H] (x : G) :
  conjugate_set x H = H :=
set.ext (λ n, ⟨λ h : _ ∈ H, by have := normal_subgroup.normal _ h x; simpa [mul_assoc] using this,
λ h, show _ ∈ H, by have := normal_subgroup.normal _ h (x⁻¹); by simpa using this⟩)

instance is_group_action.subgroup (H : set G) [is_subgroup H] (f : G → α → α) [is_group_action f] :
  is_group_action (λ x : H, f x) :=
{ one := λ a, is_group_action.one f a,
  mul := λ ⟨x, hx⟩ ⟨y, hy⟩ a, is_group_action.mul f x y a }

instance is_group_hom_conj (x : G) : is_group_hom (λ (n : G), x * n * x⁻¹) :=
⟨by simp [mul_assoc]⟩

instance is_subgroup_conj (x : G) (H : set G) [is_subgroup H] :
  is_subgroup (conjugate_set x H) :=
by rw conjugate_set_eq_image; apply_instance

/-- `dlogn p a` gives the maximum value of `n` such that `p ^ n ∣ a` -/
def dlogn (p : ℕ) : ℕ → ℕ
| 0     := 0
| (a+1) := if h : p > 1 then
  have (a + 1) / p < a + 1, from div_lt_self dec_trivial h,
    if p ∣ (a + 1) then dlogn ((a + 1) / p) + 1 else 0
  else 0

lemma dlogn_dvd {p : ℕ} : ∀ a, p > 1 → p ^ dlogn p a ∣ a
| 0     := λ _, dvd_zero _
| (a+1) := λ h,
have (a + 1) / p < a + 1, from div_lt_self dec_trivial h,
begin
  rw [dlogn, if_pos h],
  split_ifs with hd,
  { rw nat.pow_succ,
    conv { to_rhs, rw ← nat.div_mul_cancel hd },
    exact mul_dvd_mul (dlogn_dvd _ h) (dvd_refl _) },
  { simp }
end

lemma not_dvd_of_gt_dlogn {p : ℕ} : ∀ {a m}, a > 0 → p > 1 → m > dlogn p a → ¬p ^ m ∣ a
| 0     := λ m h, (lt_irrefl _ h).elim
| (a+1) := λ m h hp hm ,
have (a + 1) / p < a + 1, from div_lt_self dec_trivial hp,
begin
  rw [dlogn, if_pos hp] at hm,
  split_ifs at hm with hd,
  { have hmsub : succ (m - 1) = m := 
      succ_sub (show 1 ≤ m, from (lt_of_le_of_lt (nat.zero_le _) hm)) ▸ 
      (succ_sub_one m).symm,
    have := @not_dvd_of_gt_dlogn ((a + 1) / p) (m - 1)
      (pos_of_mul_pos_left (by rw nat.mul_div_cancel' hd; exact nat.succ_pos _) (nat.zero_le p))
      hp (lt_of_succ_lt_succ (hmsub.symm ▸ hm)),
    rwa [← nat.mul_dvd_mul_iff_right (lt_trans dec_trivial hp), nat.div_mul_cancel hd,
      ← nat.pow_succ, hmsub] at this },
  { assume h,
    exact hd (calc p = p ^ 1 : (nat.pow_one _).symm
      ... ∣ p ^ m : nat.pow_dvd_pow p hm
      ... ∣ a + 1 : h) }
end

lemma pow_dvd_of_dvd_mul {p : ℕ} : ∀ {m n k : ℕ} (hp : prime p) (hd : p ^ m ∣ n * k) (hk : ¬p ∣ k),
  p ^ m ∣ n
| 0     := by simp
| (m+1) := λ n k hp hd hk,
have hpnk : p ∣ n * k := calc p = p ^ 1 : by rw nat.pow_one
  ... ∣ p ^ (m + 1) : nat.pow_dvd_pow _ (succ_pos _)
  ... ∣ n * k : by assumption,
have hpn : p ∣ n := or.resolve_right (hp.dvd_mul.1 hpnk) hk,
have p ^ m ∣ (n / p) * k := dvd_of_mul_dvd_mul_right hp.pos $
  by rwa [mul_right_comm, nat.div_mul_cancel hpn, ← nat.pow_succ],
by rw [nat.pow_succ, ← nat.div_mul_cancel hpn];
  exact mul_dvd_mul_right (pow_dvd_of_dvd_mul hp this hk) _

lemma eq_dlogn_of_dvd_of_succ_not_dvd {a p n : ℕ} (hp : 1 < p) (h₁ : p ^ n ∣ a) (h₂ : ¬p ^ succ n ∣ a) : 
  n = dlogn p a :=
have ha : 0 < a := nat.pos_of_ne_zero (λ h, by simpa [h] using h₂),
le_antisymm (le_of_not_gt $ λ h, not_dvd_of_gt_dlogn ha hp h h₁)
  (le_of_not_gt $ λ h, h₂ $ calc p ^ succ n ∣ p ^ dlogn p a : nat.pow_dvd_pow _ h
    ... ∣ _ : dlogn_dvd _ hp)

lemma dlogn_eq_of_not_dvd {a b p  : ℕ} (hp : prime p) (hpb : ¬p ∣ b) : dlogn p a = dlogn p (a * b) :=
if ha : a = 0 then by simp [ha, dlogn] else
eq_dlogn_of_dvd_of_succ_not_dvd hp.gt_one (dvd.trans (dlogn_dvd _ hp.gt_one) (dvd_mul_right _ _))
  (λ h, not_dvd_of_gt_dlogn (nat.pos_of_ne_zero ha)
  hp.gt_one (lt_succ_self _) (pow_dvd_of_dvd_mul hp h hpb))

lemma not_dvd_div_dlogn {p a : ℕ} (ha : a > 0) (hp : p > 1) : ¬p ∣ a / (p ^ dlogn p a) :=
by rw [← nat.mul_dvd_mul_iff_left (nat.pos_pow_of_pos (dlogn p a) (lt_trans dec_trivial hp)),
    nat.mul_div_cancel' (dlogn_dvd _ hp), ← nat.pow_succ];
  exact not_dvd_of_gt_dlogn ha hp (lt_succ_self _)

class is_sylow [fintype G] (H : set G) {p : ℕ} (hp : prime p) extends is_subgroup H : Prop := 
(card_eq : card H = p ^ dlogn p (card G))

instance is_subgroup_in_subgroup (H K : set G) [is_subgroup H] [is_subgroup K] :
  is_subgroup {x : K | (x : G) ∈ H} :=
{ one_mem := show _ ∈ H, from one_mem _,
  mul_mem := λ x y hx hy, show x.1 * y.1 ∈ H, from mul_mem hx hy,
  inv_mem := λ x hx, show x.1⁻¹ ∈ H, from inv_mem hx }

lemma exists_sylow_subgroup (G : Type u) [group G] [fintype G] {p : ℕ} (hp : prime p) :
  ∃ H : set G, is_sylow H hp :=
let ⟨H, ⟨hH₁, hH₂⟩⟩ := exists_subgroup_card_pow_prime hp (dlogn_dvd (card G) hp.gt_one) in
by exactI ⟨H, by split; assumption⟩

lemma card_sylow [fintype G] (H : set G) [f : fintype H] {p : ℕ} (hp : prime p) [is_sylow H hp] :
  card H = p ^ dlogn p (card G) := 
by rw ← is_sylow.card_eq H hp; congr

lemma is_sylow_in_subgroup [fintype G] (H K : set G) {p : ℕ} (hp : prime p) [is_sylow H hp] (hsub : H ⊆ K)
  [is_subgroup K] : is_sylow {x : K | (x : G) ∈ H} hp :=
{ card_eq :=
  have h₁ : H = subtype.val '' {x : K | (x : G) ∈ H},
    from set.ext $ λ x, ⟨λ h, ⟨⟨x, hsub h⟩, ⟨h, rfl⟩⟩, λ ⟨y, hy⟩, hy.2 ▸ hy.1⟩,
  have h₂ : card K * (card G / card K) = card G := nat.mul_div_cancel' 
    ((card_eq_card_cosets_mul_card_subgroup K).symm ▸ dvd_mul_left _ _),
  have h₃ : ∀ {f : fintype {x : K | (x : G) ∈ H}}, @fintype.card {x : K | (x : G) ∈ H} f 
    = card H := λ f, by exactI
    calc @fintype.card {x : K | (x : G) ∈ H} f = card (subtype.val '' {x : K | (x : G) ∈ H}) :
      by exact (set.card_image_of_injective _ subtype.val_injective).symm
    ... = card H : set.card_eq_of_eq h₁.symm, 
  calc _ = _ : h₃ 
  ... = p ^ dlogn p (card G) : card_sylow H hp
  ... = p ^ dlogn p (card K) : congr_arg _ (h₂ ▸ eq.symm begin 
    refine dlogn_eq_of_not_dvd hp (λ h, _),
    have h₄ := mul_dvd_mul_left (card K) h,
    rw [h₂, card_eq_card_cosets_mul_card_subgroup {x : K | (x : G) ∈ H}, h₃, card_sylow H hp,
      mul_assoc, ← nat.pow_succ] at h₄,
    exact not_dvd_of_gt_dlogn (fintype.card_pos_iff.2 ⟨(1 : G)⟩) hp.gt_one (lt_succ_self _) 
      (dvd_of_mul_left_dvd h₄),
  end),
  ..sylow.is_subgroup_in_subgroup H K }

lemma sylow_conjugate [fintype G] {p : ℕ} (hp : prime p)
  (H K : set G) [is_sylow H hp] [is_sylow K hp] :
  ∃ g : G, H = conjugate_set g K :=
have hs : card (left_cosets K) = card G / (p ^ dlogn p (card G)) := 
  (nat.mul_right_inj (pos_pow_of_pos (dlogn p (card G)) hp.pos)).1
  $ by rw [← card_sylow K hp, ← card_eq_card_cosets_mul_card_subgroup, card_sylow K hp, 
    nat.div_mul_cancel (dlogn_dvd _ hp.gt_one)],
have hmodeq : card G / (p ^ dlogn p (card G)) ≡ card (fixed_points (mul_left_cosets K H)) [MOD p] := 
  hs ▸ card_modeq_card_fixed_points (mul_left_cosets K H) hp (card_sylow H hp),
have hfixed : 0 < card (fixed_points (mul_left_cosets K H)) := nat.pos_of_ne_zero 
  (λ h, (not_dvd_div_dlogn (fintype.card_pos_iff.2 ⟨(1 : G)⟩) hp.gt_one) 
    $ by rwa [h, nat.modeq.modeq_zero_iff] at hmodeq),
let ⟨⟨x, hx⟩⟩ := fintype.card_pos_iff.1 hfixed in
begin
  haveI : is_subgroup K := by apply_instance,
  revert hx,
  refine quotient.induction_on x
    (λ x hx, ⟨x, set.eq_of_card_eq_of_subset _ _⟩),
  { rw [conjugate_set_eq_image, set.card_image_of_injective _ conj_inj_left,
    card_sylow K hp, card_sylow H hp] },
  { assume y hy,
    have : (y⁻¹ * x)⁻¹ * x ∈ K := quotient.exact 
      (mem_fixed_points'.1 hx ⟦y⁻¹ * x⟧ ⟨⟨y⁻¹, inv_mem hy⟩, rfl⟩),
    simp [conjugate_set_eq_preimage, set.preimage, mul_inv_rev, *, mul_assoc] at * }
end

def conj_on_sylow [fintype G] {p : ℕ} (hp : nat.prime p)
  : Π (x : G) (H : {H : set G // is_sylow H hp}), {H : set G // is_sylow H hp} :=
λ x ⟨H, hH⟩, ⟨conjugate_set x H, by exactI
have h : is_subgroup (conjugate_set x H) := @sylow.is_subgroup_conj _ _ _ _ _,
{ card_eq := by exactI by
  rw [← card_sylow H hp, conjugate_set_eq_image, set.card_image_of_injective _ conj_inj_left],
  ..h }⟩

instance conj_on_sylow.is_group_action [fintype G] {p : ℕ} (hp : prime p) :
  is_group_action (@conj_on_sylow G _ _ _ hp) :=
{ one := λ ⟨H, hH⟩, by simp [conj_on_sylow, conjugate_set_eq_preimage, set.preimage],
  mul := λ x y ⟨H, hH⟩, by simp! [mul_inv_rev, mul_assoc, comp,
      conjugate_set_eq_image, (set.image_comp _ _ _).symm, conj_on_sylow] }

lemma card_sylow_dvd [fintype G] {p : ℕ} (hp : prime p) :
  card {H : set G // is_sylow H hp} ∣ card G :=
let ⟨H, hH⟩ := exists_sylow_subgroup G hp in
have h : orbit (conj_on_sylow hp) ⟨H, hH⟩ = set.univ :=
  set.eq_univ_iff_forall.2 (λ S, mem_orbit_iff.2 $
  let ⟨x, (hx : S.val = _)⟩ := @sylow_conjugate _ _ _ _ hp S.1 H S.2 hH in
  ⟨x, subtype.eq (hx.symm ▸ rfl)⟩),
have is_subgroup (stabilizer (conj_on_sylow hp) ⟨H, hH⟩) := group_action.is_subgroup _ _,
by exactI
have orbit_equiv : card (orbit (conj_on_sylow hp) ⟨H, hH⟩) =
  fintype.card (left_cosets (stabilizer (conj_on_sylow hp) ⟨H, hH⟩)) :=
   card_congr (orbit_equiv_left_cosets (conj_on_sylow hp) (⟨H, hH⟩ : {H : set G // is_sylow H hp})),
by exactI begin
  rw [h, ← card_congr (set.equiv_univ _)] at orbit_equiv,
  rw [orbit_equiv, card_congr (@group_equiv_left_cosets_times_subgroup _ _
    (stabilizer (conj_on_sylow hp) ⟨H, hH⟩) (by apply_instance)), card_prod],
  exact dvd_mul_right _ _
end

lemma card_sylow_modeq_one [fintype G] {p : ℕ} (hp : prime p) :
  card {H : set G // is_sylow H hp} ≡ 1 [MOD p] :=
let ⟨H, hH⟩ := exists_sylow_subgroup G hp in
by exactI
eq.trans
(card_modeq_card_fixed_points (λ x : H, conj_on_sylow hp (x : G)) hp (card_sylow H hp))
begin
  refine congr_fun (show (%) _ = (%) 1, 
    from congr_arg _ (fintype.card_eq_one_iff.2 _)) p,
  refine ⟨(⟨(⟨H, hH⟩ :  {H // is_sylow H hp}), λ ⟨x, hx⟩, subtype.eq $
    set.ext (λ i, by simp [conj_on_sylow, conjugate_set_eq_preimage, mul_mem_cancel_left _ hx,
      mul_mem_cancel_right _ (inv_mem hx)])⟩ :
        subtype (fixed_points (λ (x : ↥H), conj_on_sylow hp ↑x))), _⟩,
  refine λ L, subtype.eq (subtype.eq _),
  rcases L with ⟨⟨L, hL₁⟩, hL₂⟩,
  have Hsub : H ⊆ normalizer L,
  { assume x hx n,
    conv {to_rhs, rw ← subtype.mk.inj (hL₂ ⟨x, hx⟩)},
    simp [conjugate_set, mul_assoc] },
  suffices : ∀ x, x ∈ {x : normalizer L | (x : G) ∈ L} ↔ x ∈ {x : normalizer L | (x : G) ∈ H},
  { exact set.ext (λ x, ⟨λ h, (this ⟨x, subset_normalizer _ h⟩).1 h, λ h, (this ⟨x, Hsub h⟩).2 h⟩) },
  assume x,
  haveI := is_sylow_in_subgroup L (normalizer L) hp (subset_normalizer L),
  haveI := is_sylow_in_subgroup H (normalizer L) hp Hsub,
  cases sylow_conjugate hp {x : normalizer L | (x : G) ∈ H} {x | (x : G) ∈ L} with x hx,
  simp [hx]
end
