// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2_int(s: Seq<char>) -> nat
  decreases s.len()
{
  if s.len() == 0 { 
    0nat 
  } else { 
    if valid_bit_string(s) {
      2 * str2_int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
    } else {
      0nat
    }
  }
}

spec fn exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 { 1nat } else { x * exp_int(x, (y - 1) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

spec fn all_zero(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0'
}

fn add(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2),
  ensures 
    valid_bit_string(res) &&
    str2_int(res) == str2_int(s1) + str2_int(s2),
{
  assume(false);
  unreached()
}

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (quotient_remainder: (Seq<char>, Seq<char>))
  requires 
    valid_bit_string(dividend) && valid_bit_string(divisor) &&
    str2_int(divisor) > 0,
  ensures 
    valid_bit_string(quotient_remainder.0) && valid_bit_string(quotient_remainder.1) &&
    str2_int(quotient_remainder.0) == str2_int(dividend) / str2_int(divisor) &&
    str2_int(quotient_remainder.1) == str2_int(dividend) % str2_int(divisor),
{
  assume(false);
  unreached()
}

fn zeros(n: nat) -> (s: Seq<char>)
  ensures 
    s.len() == n &&
    valid_bit_string(s) &&
    str2_int(s) == 0 &&
    all_zero(s),
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Fixed type mismatch in Seq::new closure by changing `nat` to `int` for the closure variable `i`. */
spec fn nat_to_bit_seq(n: nat) -> Seq<char>
  decreases n
{
  if n == 0 { Seq::<char>::new(1, |i: int| '0') }
  else if n == 1 { Seq::<char>::new(1, |i: int| '1') }
  else {
    let remainder: nat = (n % 2) as nat;
    let quotient: nat = (n / 2) as nat;
    if remainder == 0 {
      nat_to_bit_seq(quotient) + Seq::<char>::new(1, |i: int| '0')
    } else {
      nat_to_bit_seq(quotient) + Seq::<char>::new(1, |i: int| '1')
    }
  }
}
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Seq<char>, sy: Seq<char>, sz: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz) &&
    sy.len() > 0 && str2_int(sz) > 1,
  ensures 
    valid_bit_string(res) &&
    str2_int(res) == exp_int(str2_int(sx), str2_int(sy)) % str2_int(sz),
  decreases sy.len(),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Fixed type mismatch error E0308 and E0631 by changing the closure argument type from `nat` to `int` in `Seq::<char>::new` as required by the `Fn(vstd::prelude::int)` bound, and addressed other `nat` vs `int` mismatches.*/
{
  let x_nat = str2_int(sx);
  let y_nat = str2_int(sy);
  let z_nat = str2_int(sz);

  if y_nat == 0 {
    return Seq::<char>::new(1, |i: int| '1'); // x^0 = 1
  }

  // Convert 2 to a bit string represented by Seq<char>
  let two_bit_seq = Seq::<char>::new(1, |i: int| '1') + Seq::<char>::new(1, |i: int| '0');
  let (y_div2_seq, y_mod2_seq) = div_mod(sy, two_bit_seq); // Divide sy by 2
  let is_even = str2_int(y_mod2_seq) == 0;

  let r = mod_exp(sx, y_div2_seq, sz); // Recursive call: mod_exp(x, y/2, z)
  let r_nat = str2_int(r);

  let term1_nat: nat = (r_nat * r_nat) % z_nat;
  
  if is_even {
    nat_to_bit_seq(term1_nat)
  } else {
    let product_nat: nat = (term1_nat * (x_nat % z_nat)) % z_nat;
    nat_to_bit_seq(product_nat)
  }
}
// </vc-code>


}

fn main() {}