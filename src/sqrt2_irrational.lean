import data.int.parity
import data.nat.prime
import tactic

open nat
theorem sqrt2_irrational (a b : ℕ) (rel_prime : nat.gcd a b = 1) : a * a ≠ 2 * b * b :=
begin 
  /- We prove this by contradiction.
     Suppose there are a, b such that a * a = 2 * b * b -/
  by_contradiction,

  /- first, show that a is even -/
  have a2_even: 2 ∣ a*a,
    rw h,
    rw mul_assoc,
    exact dvd.intro (b * b) rfl,
  
  have a_even : 2 ∣ a,    
    rw nat.prime.dvd_mul nat.prime_two at a2_even,
    cases a2_even, exact a2_even, exact a2_even,
  have a_even_copy : 2 ∣ a, exact a_even,

  have two_not_0 : 2 ≠ 0, from ne_zero.ne 2,

  /- then, we write a = 2 * a' and obtain 2 * a' * a' = b * b -/

  /-
  cases a_even with a' j,
  have h': 2 * a' * a' = b * b, -- it is such a pain to even derive this simple fact
    rw j at h,
    ring_nf at h,
    rw (_ : 4 = 2*2) at h, rw mul_assoc at h,
    sorry,
  -/

  cases a_even with a' j,
  rw j at h,

  have h': 2 * a'^2 = b^2, -- it is such a pain to even derive this simple fact
    ring_nf at h,
    rw (_ : 4 = 2*2) at h, rw mul_assoc at h,
    exact (mul_right_inj' two_not_0).mp h,
    refl,


  /- then, we show that b is even -/
  have b2_even : 2 ∣ b^2,
    rw ←h',
    exact dvd.intro (a'^2) rfl,

  have b2_even' : 2 ∣ b*b,
    sorry,
  
  have b_even : 2 ∣ b,
    rw nat.prime.dvd_mul nat.prime_two at b2_even',
    cases b2_even', exact b2_even', exact b2_even',
  
  have both_even : 2 ∣ (nat.gcd a b),
    rw nat.dvd_gcd_iff,
    split, exact a_even_copy, exact b_even,

  rw rel_prime at both_even,
  have : 2 = 1,
    exact nat.dvd_one.mp both_even, 
  linarith,
end
