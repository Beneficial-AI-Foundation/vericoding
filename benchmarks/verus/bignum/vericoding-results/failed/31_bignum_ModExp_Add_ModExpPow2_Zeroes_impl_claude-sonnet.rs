// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
  decreases s.len()
{
  if s.len() == 0 { 
      0nat 
  } else { 
      2nat * str2int(s.subrange(0, s.len() as int - 1)) + (if s[s.len() as int - 1] == '1' { 1nat } else { 0nat })
  }
}

spec fn exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 { 1nat } else { x * exp_int(x, (y - 1nat) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
}

spec fn all_zero(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0'
}

fn add(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
      valid_bit_string(s1) && valid_bit_string(s2),
  ensures 
      valid_bit_string(res),
      str2int(res) == str2int(s1) + str2int(s2),
{
  assume(false);
  unreached()
}

fn mod_exp_pow2(sx: Seq<char>, sy: Seq<char>, n: nat, sz: Seq<char>) -> (res: Seq<char>)
  requires 
      valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz),
      str2int(sy) == exp_int(2nat, n) || str2int(sy) == 0,
      sy.len() == n + 1,
      str2int(sz) > 1,
  ensures 
      valid_bit_string(res),
      str2int(res) == exp_int(str2int(sx), str2int(sy)) % str2int(sz),
  decreases n
{
  assume(false);
  unreached()
}

fn zeros(n: nat) -> (s: Seq<char>)
  ensures 
      s.len() == n,
      valid_bit_string(s),
      str2int(s) == 0,
      all_zero(s),
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): no additional helpers needed, using only basic operations */
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Seq<char>, sy: Seq<char>, sz: Seq<char>) -> (res: Seq<char>)
  requires 
      valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz),
      sy.len() > 0 && str2int(sz) > 1,
  ensures 
      valid_bit_string(res),
      str2int(res) == exp_int(str2int(sx), str2int(sy)) % str2int(sz),
  decreases sy.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): fix compilation errors by removing int casts in subrange calls */
    if sy.len() == 1 {
        if sy@[0] == '0' {
            let one = seq!['1'];
            one
        } else {
            let sx_mod = mod_exp_pow2(sx, sy, 0, sz);
            sx_mod
        }
    } else {
        let sy_half_len = sy.len() / 2;
        let sy_low = sy.subrange(sy_half_len, sy.len());
        let sy_high = sy.subrange(0, sy_half_len);
        
        let res_low = mod_exp(sx, sy_low, sz);
        
        let power_of_two = zeros(sy_half_len);
        let power_of_two_with_one = power_of_two.push('1');
        
        let res_high_exp = mod_exp_pow2(res_low, power_of_two_with_one, sy_half_len, sz);
        let final_high = mod_exp(sx, sy_high, sz);
        
        let temp = mod_exp_pow2(final_high, power_of_two_with_one, sy_half_len, sz);
        let result = add(res_high_exp, temp);
        
        mod_exp_pow2(result, seq!['1'], 0, sz)
    }
}
// </vc-code>


}

fn main() {}