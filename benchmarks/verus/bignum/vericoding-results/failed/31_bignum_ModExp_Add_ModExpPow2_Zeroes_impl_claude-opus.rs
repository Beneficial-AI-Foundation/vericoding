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
    /* code modified by LLM (iteration 10): Fixed type errors by using usize instead of int for indexing */
    if sy.len() == 1 && sy[0] == '0' {
        let res = zeros(1nat);
        proof {
            assert(str2int(sy) == 0);
            assert(exp_int(str2int(sx), 0nat) == 1nat);
            assert(str2int(res) == 0);
            assert(1nat % str2int(sz) == 1nat) by {
                assert(str2int(sz) > 1);
            }
        }
        let mut result = zeros(1nat);
        result = result.update(0, '1');
        proof {
            assert(result.len() == 1);
            assert(result[0] == '1');
            assert(str2int(result) == 1nat);
        }
        return result;
    } else if sy[sy.len() - 1] == '0' {
        let sy_len_minus_1: usize = sy.len() - 1;
        let sy_half = sy.subrange(0, sy_len_minus_1 as int);
        proof {
            assert(str2int(sy) == 2nat * str2int(sy_half));
            assert(exp_int(str2int(sx), str2int(sy)) == exp_int(exp_int(str2int(sx), 2nat), str2int(sy_half)));
        }
        let sx_squared = mod_exp_pow2(sx, zeros(2nat).push('1'), 1nat, sz);
        return mod_exp(sx_squared, sy_half, sz);
    } else {
        let sy_len_minus_1: usize = sy.len() - 1;
        let sy_minus_one = sy.subrange(0, sy_len_minus_1 as int).push('0');
        proof {
            assert(sy[sy.len() - 1] == '1');
            assert(str2int(sy) == 2nat * str2int(sy.subrange(0, sy_len_minus_1 as int)) + 1nat);
            assert(str2int(sy_minus_one) == str2int(sy) - 1nat);
            assert(exp_int(str2int(sx), str2int(sy)) == str2int(sx) * exp_int(str2int(sx), (str2int(sy) - 1nat) as nat));
        }
        let temp = mod_exp(sx, sy_minus_one, sz);
        let result = mod_exp_pow2(temp, add(sx, zeros(sx.len())), 0nat, sz);
        return result;
    }
}
// </vc-code>


}

fn main() {}