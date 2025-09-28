// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
  recommends valid_bit_string(s)
  decreases s.len()
{
  if s.len() == 0 {
    0nat
  } else {
    2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
  }
}

spec fn exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 { 1nat } else { x * exp_int(x, (y - 1) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

fn add(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2)
  ensures 
    valid_bit_string(res),
    str2int(res) == str2int(s1) + str2int(s2)
{
  assume(false);
  unreached()
}

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (res: (Seq<char>, Seq<char>))
  requires 
    valid_bit_string(dividend) && valid_bit_string(divisor),
    str2int(divisor) > 0
  ensures 
    valid_bit_string(res.0) && valid_bit_string(res.1),
    str2int(res.0) == str2int(dividend) / str2int(divisor),
    str2int(res.1) == str2int(dividend) % str2int(divisor)
{
  assume(false);
  unreached()
}

fn mod_exp_pow2(sx: Seq<char>, sy: Seq<char>, n: nat, sz: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz),
    str2int(sy) == exp_int(2nat, n) || str2int(sy) == 0,
    sy.len() == n + 1,
    str2int(sz) > 1
  ensures 
    valid_bit_string(res),
    str2int(res) == exp_int(str2int(sx), str2int(sy)) % str2int(sz)
  decreases n
{
  assume(false);
  unreached()
}

fn mul(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2)
  ensures 
    valid_bit_string(res),
    str2int(res) == str2int(s1) * str2int(s2)
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Removed `spec` keyword from the `to_seq_char` helper function to make it compliant with `nat` and `int` types, as it is used in executable code. */
fn to_seq_char(v: nat) -> (res: Seq<char>)
  ensures valid_bit_string(res) && str2int(res) == v
  decreases v
{
  if v == 0 {
    seq!['0']
  } else {
    let remainder = v % 2;
    let quotient = v / 2;
    let mut result_seq = if quotient == 0 { Seq::empty() } else { to_seq_char(quotient) };
    result_seq + seq![if remainder == 1 { '1' } else { '0' }]
  }
}
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Seq<char>, sy: Seq<char>, sz: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz),
    sy.len() > 0 && str2int(sz) > 1
  ensures 
    valid_bit_string(res),
    str2int(res) == exp_int(str2int(sx), str2int(sy)) % str2int(sz)
  decreases sy.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Fixed type casting issues by removing the `as int` casts after changing `to_seq_char` from `spec fn` to `fn`. This resolution correctly aligns `nat` types for comparison with `0nat`. */
{
  // Base case: If sy is "0", result is 1 % sz, which is 1 if sz > 1
  let sy_nat = str2int(sy);
  if sy_nat == 0 {
    let one_char_seq = seq!['1'];
    proof {
      assert(str2int(seq!['1']) == 1nat);
      assert(1nat % str2int(sz) == 1nat) by (nonlinear_arith);
    }
    return one_char_seq;
  }

  // Recursive step
  // sy_div_2 and sy_mod_2 are results from div_mod, which returns a tuple.
  let (sy_div_2_seq, sy_mod_2_seq) = div_mod(sy, seq!['1', '0']);
  let temp_res_seq = mod_exp(sx, sy_div_2_seq, sz);
  let temp_val_nat = str2int(temp_res_seq);

  let sx_val_nat = str2int(sx);
  let sz_val_nat = str2int(sz);

  let sy_mod_2_nat = str2int(sy_mod_2_seq);

  if sy_mod_2_nat == 0 { // sy is even
    let squared_val_nat = (temp_val_nat * temp_val_nat) % sz_val_nat;
    proof {
        assert(exp_int(sx_val_nat, (str2int(sy_div_2_seq) as nat) * 2nat) == exp_int(exp_int(sx_val_nat, (str2int(sy_div_2_seq) as nat)), 2nat)) by(nonlinear_arith);
        assert(str2int(temp_res_seq) == exp_int(sx_val_nat, (str2int(sy_div_2_seq) as nat)) % sz_val_nat);
        assert(exp_int(sx_val_nat, sy_nat) % sz_val_nat == (str2int(temp_res_seq) * str2int(temp_res_seq)) % sz_val_nat) by(nonlinear_arith);
    }
    to_seq_char(squared_val_nat)
  } else { // sy is odd
    let val_to_mult_nat = (temp_val_nat * temp_val_nat) % sz_val_nat;
    let final_val_nat = (val_to_mult_nat * sx_val_nat) % sz_val_nat;
    proof {
        assert(exp_int(sx_val_nat, (str2int(sy_div_2_seq) as nat) * 2nat + 1nat) == exp_int(exp_int(sx_val_nat, (str2int(sy_div_2_seq) as nat)), 2nat) * sx_val_nat) by(nonlinear_arith);
        assert(str2int(temp_res_seq) == exp_int(sx_val_nat, (str2int(sy_div_2_seq) as nat)) % sz_val_nat);
        assert(exp_int(sx_val_nat, sy_nat) % sz_val_nat == ((str2int(temp_res_seq) * str2int(temp_res_seq)) % sz_val_nat * sx_val_nat) % sz_val_nat) by(nonlinear_arith);
    }
    to_seq_char(final_val_nat)
  }
}
// </vc-code>


}

fn main() {}