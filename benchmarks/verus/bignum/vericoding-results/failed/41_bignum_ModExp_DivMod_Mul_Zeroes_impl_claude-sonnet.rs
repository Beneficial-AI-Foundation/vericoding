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
/* helper modified by LLM (iteration 10): Fixed nat/int literal suffixes */
proof fn exp_int_mod_properties()
    ensures
        forall|x: nat, y: nat, m: nat| m > 1 ==> {
            let base_case = if y == 0 { 1nat % m } else { (x % m) * exp_int(x, (y - 1) as nat) % m };
            exp_int(x, y) % m == base_case
        }
{
}

proof fn str2int_empty_is_zero()
    ensures str2int(seq![]) == 0
{
}

proof fn valid_bit_string_subrange(s: Seq<char>, start: int, end: int)
    requires valid_bit_string(s), 0 <= start <= end <= s.len()
    ensures valid_bit_string(s.subrange(start, end))
{
}

fn is_zero(s: Seq<char>) -> (result: bool)
    requires valid_bit_string(s)
    ensures result == (str2int(s) == 0)
{
    s.len() == 0 || (s.len() == 1 && s.index(0) == '0')
}

fn bit_string_from_nat(n: usize) -> (s: Seq<char>)
    ensures valid_bit_string(s)
{
    if n == 1 {
        seq!['1']
    } else {
        seq!['0']
    }
}
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
    /* code modified by LLM (iteration 10): Fixed nat/int literal suffixes */
    if is_zero(sy) {
        bit_string_from_nat(1)
    } else {
        let ghost last_bit = sy.index((sy.len() - 1) as int);
        let ghost sy_prefix = sy.subrange(0, (sy.len() - 1) as int);
        
        let recursive_result = mod_exp(sx, sy_prefix, sz);
        let squared = mul(recursive_result, recursive_result);
        let (_, mod_squared) = div_mod(squared, sz);
        
        if last_bit == '0' {
            mod_squared
        } else {
            let temp = mul(mod_squared, sx);
            let (_, final_mod) = div_mod(temp, sz);
            final_mod
        }
    }
}
// </vc-code>


}

fn main() {}