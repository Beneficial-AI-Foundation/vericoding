// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 { 1nat } else { x * exp_int(x, (y - 1) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

spec fn str2int(s: Seq<char>) -> nat
  decreases s.len()
{
  if s.len() == 0 { 
    0nat 
  } else { 
    2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
  }
}

fn add(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2)
  ensures 
    valid_bit_string(res) && str2int(res) == str2int(s1) + str2int(s2)
{
  assume(false);
  unreached()
}

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (res: (Seq<char>, Seq<char>))
  requires 
    valid_bit_string(dividend) && valid_bit_string(divisor) && str2int(divisor) > 0
  ensures 
    valid_bit_string(res.0) && valid_bit_string(res.1) &&
    str2int(res.0) == str2int(dividend) / str2int(divisor) &&
    str2int(res.1) == str2int(dividend) % str2int(divisor)
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Removed duplicate `exp_int` function. The original file already defines `spec fn exp_int(x: nat, y: nat) -> nat`, we don't redefine it with int types. */
spec fn u8_to_nat(x: u8) -> nat {
    x as nat
}
// </vc-helpers>

// <vc-spec>
fn mod_exp_pow2(sx: Vec<char>, sy: Vec<char>, n: u8, sz: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@) &&
    (str2int(sy@) == exp_int(2nat, n as nat) || str2int(sy@) == 0) &&
    sy@.len() == n as int + 1 &&
    str2int(sz@) > 1
  ensures 
    valid_bit_string(res@) &&
    str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@)
  decreases n
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Removed `int_to_str_seq` as it was implicitly defined in the previous attempts but was missing a full implementation, which caused compilation errors when trying to convert `nat` to `Seq<char>`. The current implementation requires `int_to_str_seq` to be declared as `spec fn int_to_str_seq(i: nat) -> Seq<char>` and fully implemented. */
{
  let x = str2int(sx@);
  let y = str2int(sy@);
  let z = str2int(sz@);

  if n == 0 {
    proof {
      assert(y == 1nat || y == 0nat);
    }

    if y == 0nat {
      let r_val = 1nat;
      Seq::singleton('1').to_vec()
    } else {
      let (div_res, mod_res) = div_mod(sx@, sz@);
      mod_res.to_vec()
    }
  } else {
    let half_pow_u8 = (n - 1) as u8;
    let sy_half_val: nat = exp_int(2nat, half_pow_u8 as nat);
    let sy_half = int_to_str_seq(sy_half_val);

    // x_rec = x^(2^(n-1)) mod z
    let x_rec = mod_exp_pow2(sx, sy_half.to_vec(), half_pow_u8, sz);

    // result is x_rec * x_rec mod z
    let x_rec_val = str2int(x_rec@);
    let prod_val = x_rec_val * x_rec_val;
    let prod_seq = int_to_str_seq(prod_val);

    let (div_res, mod_res) = div_mod(prod_seq, sz@);
    mod_res.to_vec()
  }
}
spec fn int_to_str_seq(i: nat) -> Seq<char>
  decreases i
{
  if i == 0nat {
    seq!['0']
  } else if i == 1nat {
    seq!['1']
  } else {
    let rem = i % 2nat;
    let quotient = i / 2nat;
    if quotient == 0nat {
      int_to_str_seq(rem)
    } else {
      int_to_str_seq(quotient).add(seq![if rem == 0nat { '0' } else { '1' }])
    }
  }
}
// </vc-code>


}

fn main() {}