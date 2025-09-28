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

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (result: (Seq<char>, Seq<char>))
  requires
      valid_bit_string(dividend) && valid_bit_string(divisor) &&
      str2int(divisor) > 0
  ensures
      valid_bit_string(result.0) && valid_bit_string(result.1) &&
      str2int(result.0) == str2int(dividend) / str2int(divisor) &&
      str2int(result.1) == str2int(dividend) % str2int(divisor)
{
  assume(false);
  unreached()
}

fn mul(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires valid_bit_string(s1) && valid_bit_string(s2)
  ensures
      valid_bit_string(res) &&
      str2int(res) == str2int(s1) * str2int(s2)
{
  assume(false);
  unreached()
}

fn zeros(n: nat) -> (s: Seq<char>)
  ensures
      s.len() == n &&
      valid_bit_string(s) &&
      str2int(s) == 0 &&
      all_zero(s)
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Seq<char>, sy: Seq<char>, sz: Seq<char>) -> (res: Seq<char>)
  requires
      valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz) &&
      sy.len() > 0 && str2int(sz) > 1
  ensures
      valid_bit_string(res) &&
      str2int(res) == exp_int(str2int(sx), str2int(sy)) % str2int(sz)
  decreases sy.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): Fixed parentheses in loop invariant expression */
    if sy.len() == 1 && sy[0] == '0' {
        let one = seq!['1'];
        proof {
            assert(str2int(sy) == 0);
            assert(exp_int(str2int(sx), 0) == 1);
        }
        return div_mod(one, sz).1;
    } else if sy.len() == 1 && sy[0] == '1' {
        proof {
            assert(str2int(sy) == 1);
            assert(exp_int(str2int(sx), 1) == str2int(sx));
        }
        return div_mod(sx, sz).1;
    } else {
        let sy_half = if sy[sy.len() - 1] == '0' {
            sy.subrange(0, sy.len() - 1)
        } else {
            let mut sy_half = sy.subrange(0, sy.len() - 1);
            let mut i: usize = sy_half.len() - 1;
            loop
                invariant
                    i <= sy_half.len() - 1,
                    forall|j: int| (i as int) < j < (sy_half.len() as int) ==> sy_half[j] == '0',
                    valid_bit_string(sy_half)
            {
                if sy_half[i as int] == '0' {
                    sy_half = sy_half.update(i as int, '1');
                    break;
                } else {
                    sy_half = sy_half.update(i as int, '0');
                    if i == 0 {
                        break;
                    }
                    i = i - 1;
                }
            }
            sy_half
        };
        
        let half_result = mod_exp(sx, sy_half, sz);
        let squared = mul(half_result, half_result);
        let squared_mod = div_mod(squared, sz).1;
        
        if sy[sy.len() - 1] == '0' {
            proof {
                assert(str2int(sy) == 2 * str2int(sy_half));
                assert(exp_int(str2int(sx), str2int(sy)) == 
                       exp_int(str2int(sx), str2int(sy_half)) * 
                       exp_int(str2int(sx), str2int(sy_half)));
            }
            squared_mod
        } else {
            let result_mul = mul(squared_mod, sx);
            let result = div_mod(result_mul, sz).1;
            proof {
                assert(str2int(sy) == 2 * str2int(sy_half) + 1);
                assert(exp_int(str2int(sx), str2int(sy)) == 
                       exp_int(str2int(sx), str2int(sy_half)) * 
                       exp_int(str2int(sx), str2int(sy_half)) * 
                       str2int(sx));
            }
            result
        }
    }
}
// </vc-code>


}

fn main() {}