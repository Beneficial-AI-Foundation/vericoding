// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
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

spec fn all_zero(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0'
}

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (res: (Seq<char>, Seq<char>))
  requires 
      valid_bit_string(dividend) && valid_bit_string(divisor),
      str2int(divisor) > 0,
  ensures 
      valid_bit_string(res.0) && valid_bit_string(res.1),
      str2int(res.0) == str2int(dividend) / str2int(divisor),
      str2int(res.1) == str2int(dividend) % str2int(divisor),
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
/* helpers modified by LLM (iteration 10): Fix recursive mod_exp_helper with proper binary conversion using leaves recomputation */
proof fn mod_exp_helper(sx: Seq<char>, sy: Seq<char>, sz: Seq<char>) -> (res: Seq<char>)
    requires
        valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz),
        str2int(sz) > 1,
    ensures
        valid_bit_string(res),
        str2int(res) == exp_int(str2int(sx), str2int(sy)) % str2int(sz),
    decreases sy.len()
{
    if sy.len() == 0 {
        // 1 mod m = 1 (if m > 1)
        Vec::new().push('1').view()
    } else {
        let new_sy = sy.subrange(0, sy.len() - 1);
        let temp = mod_exp_helper(sx, new_sy, sz);
        let digit = sy[sy.len() - 1];
        let temp_val = str2int(temp);
        let square_mod = (temp_val * temp_val) % str2int(sz);
        
        if digit == '1' {
            let result_val = (square_mod * str2int(sx)) % str2int(sz);
            // Convert result_val to binary string
            let mut value = result_val;
            let mut bits = Vec::new();
            while value > 0 {
                if value % 2 == 1 {
                    bits.push('1');
                } else {
                    bits.push('0');
                }
                value = value / 2;
            }
            bits.reverse();
            bits.view()
        } else {
            // Convert square_mod to binary string
            let mut value = square_mod;
            let mut bits = Vec::new();
            while value > 0 {
                if value % 2 == 1 {
                    bits.push('1');
                } else {
                    bits.push('0');
                }
                value = value / 2;
            }
            bits.reverse();
            bits.view()
        }
    }
}

fn seq_to_vec(s: Seq<char>) -> (v: Vec<char>)
    ensures
        v@ == s,
        valid_bit_string(v@)
{
    let mut vec = Vec::new();
    let mut index: usize = 0;
    while index < s.len() as usize
        invariant
            0 <= index <= s.len(),
            vec@ == s.subrange(0, index as int),
            valid_bit_string(vec@)
    {
        vec.push(s[index as int]);
        index += 1;
    }
    vec
}
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Vec<char>, sy: Vec<char>, sz: Vec<char>) -> (res: Vec<char>)
  requires 
      valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@),
      sy.len() > 0 && str2int(sz@) > 1,
  ensures 
      valid_bit_string(res@),
      str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@),
  decreases sy.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Handle conversion and empty result case */
{
    proof {
        let result_seq = mod_exp_helper(sx@, sy@, sz@);
        assert(valid_bit_string(result_seq));
        assert(str2int(result_seq) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@));
    }
    
    let result_seq = mod_exp_helper(sx@, sy@, sz@);
    if result_seq.len() == 0 {
        // If result is 0, return a single '0'
        Vec::new().push('0')
    } else {
        seq_to_vec(result_seq)
    }
}
// </vc-code>


}

fn main() {}