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

spec fn valid_bit_string(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}
// </vc-preamble>

// <vc-helpers>

/* helper modified by LLM (iteration 10): Fixed function signature syntax error */
proof fn mul_recursive_precise(s1: Seq<char>, s2: Seq<char>, carry: nat) -> (Seq<char>, nat)
  requires
    valid_bit_string(s1) && valid_bit_string(s2),
    carry == 0 || carry == 1
  ensures
    valid_bit_string(res.0),
    res.1 == 0 || res.1 == 1,
    str2int(res.0) + (2 as nat).pow(s1.len() as nat) * res.1 == str2int(s1) + str2int(s2) + carry
  decreases s1.len()
{
  if s1.len() == 0 {
    if carry == 1 {
      if s2.len() == 0 {
        (seq!['1'], 0)
      } else {
        let first_char = s2[0];
        let rest = s2.subrange(1, s2.len());
        if first_char == '0' {
          (seq!['1'] + rest, 0)
        } else {
          (seq!['0'], 1)
        }
      }
    } else {
      (s2, 0)
    }
  } else {
    let s1_first = s1[0];
    let s1_rest = s1.subrange(1, s1.len());
    let s2_first = if s2.len() > 0 { s2[0] } else { '0' };
    let s2_rest = if s2.len() > 0 { s2.subrange(1, s2.len()) } else { s2 };
    let sum_bits = (if s1_first == '1' { 1 } else { 0 }) + (if s2_first == '1' { 1 } else { 0 }) + carry;
    let current_bit = if sum_bits % 2 == 0 { '0' } else { '1' };
    let next_carry = sum_bits / 2;
    let (rest_bits, final_carry) = mul_recursive_precise(s1_rest, s2_rest, next_carry);
    (seq![current_bit] + rest_bits, final_carry)
  }
}
// </vc-helpers>

// <vc-spec>
fn mul(s1: Vec<char>, s2: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(s1@) && valid_bit_string(s2@)
  ensures 
    valid_bit_string(res@) &&
    str2int(res@) == str2int(s1@) * str2int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): Implemented multiplication using recursive helper function */
    if s1.len() == 0 || s2.len() == 0 {
        vec!['0']
    } else {
        let (result_seq, final_carry) = mul_recursive_precise(s1@, s2@, 0);
        let result = Vec::from_seq(result_seq);
        if final_carry == 1 {
            let mut extended = vec!['1'];
            extended.extend(result);
            extended
        } else {
            result
        }
    }
}
// </vc-code>


}

fn main() {}