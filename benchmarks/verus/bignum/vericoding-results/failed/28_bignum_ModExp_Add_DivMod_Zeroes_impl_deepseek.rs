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
/* helper modified by LLM (iteration 10): fix syntax and use proper proof function structure */
proof fn mod_exp_helper(x: nat, y: nat, z: nat) -> (r: nat)
  requires
    z > 1,
  ensures
    r == exp_int(x, y) % z,
  decreases y,
{
  if y == 0 {
    1nat % z
  } else {
    let prev = mod_exp_helper(x, (y - 1) as nat, z);
    (x * prev) % z
  }
}

proof fn nat_usize_conversion(n: nat) -> (res: usize)
  requires n as int <= usize::MAX as int,
  ensures res as int == n as int,
{
  n as usize
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
/* code modified by LLM (iteration 10): fix last_char index calculation */
{
    let y_len: usize = sy.len() as usize;
    if y_len == 0 {
        zeros(1nat)
    } else {
        let last_char_index: usize = y_len - 1;
        let last_char = sy[last_char_index as int];
        if last_char == '1' {
            let (_, r) = div_mod(sx, sz);
            let temp_seq = zeros(1nat);
            let (_, r2) = div_mod(add(r, temp_seq), sz);
            r2
        } else {
            zeros(1nat)
        }
    }
}
// </vc-code>


}

fn main() {}