// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2_int(s: Seq<char>) -> nat
  decreases s.len()
{
  if s.len() == 0 { 0nat } else { 2nat * str2_int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat }) }
}

spec fn exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 { 1nat } else { x * exp_int(x, (y - 1nat) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
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

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (res: (Seq<char>, Seq<char>))
  requires 
    valid_bit_string(dividend) && valid_bit_string(divisor) &&
    str2_int(divisor) > 0,
  ensures 
    valid_bit_string(res.0) && valid_bit_string(res.1) &&
    str2_int(res.0) == str2_int(dividend) / str2_int(divisor) &&
    str2_int(res.1) == str2_int(dividend) % str2_int(divisor),
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Fixed `to_vec()` errors by replacing `add` with `+ Seq::new(1, x)` for `Seq<char>` concatenation, as `add` returns `Seq<char>` and not `char` for the second argument. Explicitly concatenated single-character sequences. */
spec fn nat_to_seq_char_recursive_rev(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 { seq![] }
    else {
        let (q, r) = (n / 2, (n % 2) as nat);
        let next_char = if r == 0 { '0' } else { '1' };
        nat_to_seq_char_recursive_rev(q) + Seq::new(1, |i| next_char)
    }
}

spec fn str2_seq(n: nat) -> Seq<char>
    recommends n >= 0
{
    if n == 0 { seq!['0'] } else { nat_to_seq_char_recursive_rev(n) }
}
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Vec<char>, sy: Vec<char>, sz: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@) &&
    sy@.len() > 0 && str2_int(sz@) > 1,
  ensures 
    valid_bit_string(res@) &&
    str2_int(res@) == exp_int(str2_int(sx@), str2_int(sy@)) % str2_int(sz@),
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Fixed `to_vec()` and `to_Seq()` errors by replacing them with `@` for sequence access. Also, changed `1_nat` to `1` as `nat` is not a valid suffix for integer literals. */
{
  use std::ops::Index;
  if sy.len() == 1 && *sy.index(0) == '0' {
    let one_seq: Seq<char> = seq!['1'];
    let (_, remainder) = div_mod(one_seq, sz@);
    remainder.to_vec()
  } else {
    let (y_div2_seq_val, y_mod2_seq_val) = div_mod(sy@, seq!['1', '0']);
    let result_half_vec = mod_exp(sx.clone(), y_div2_seq_val.to_vec(), sz.clone());
    let result_half_int = str2_int(result_half_vec@);
    let q_pow2_int = result_half_int * result_half_int;
    let (q_pow2_seq, r_pow2_seq) = div_mod(str2_seq(q_pow2_int), sz@);
    let mut final_result_seq = r_pow2_seq;
    if str2_int(y_mod2_seq_val) == 1 {
      let (q_x_seq, r_x_seq) = div_mod(sx@, sz@);
      let r_x_int = str2_int(r_x_seq);
      let mult_int = str2_int(final_result_seq) * r_x_int;
      let (q_mult_seq, r_mult_seq) = div_mod(str2_seq(mult_int), sz@);
      final_result_seq = r_mult_seq;
    }
    final_result_seq.to_vec()
  }
}
// </vc-code>


}

fn main() {}