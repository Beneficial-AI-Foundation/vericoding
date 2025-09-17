use vstd::prelude::*;

verus! {

spec fn Str2Int(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
  if s.len() == 0 {
    0
  } else {
    2 * Str2Int(s.subrange(0, s.len() as int - 1))
      + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat })
  }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
  // All characters must be '0' or '1'.
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
/* helper modified by LLM (iteration 4): changed types in add_bits to use usize to avoid 'int'/'nat' in exec code */
fn add_bits(a: char, b: char, carry: usize) -> (char, usize) {
    let a_val = if a == '0' { 0 } else { 1 };
    let b_val = if b == '0' { 0 } else { 1 };
    let sum = a_val + b_val + carry;
    let bit = if sum % 2 == 0 { '0' } else { '1' };
    let new_carry = sum / 2;
    (bit, new_carry)
}
// </vc-helpers>

// <vc-spec>
exec fn Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@),
   ValidBitString(s2@),
  ensures ValidBitString(res@), 
    Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): changed carry type to usize and updated add_bits call */
    let len1 = s1.len();
    let len2 = s2.len();
    let mut carry: usize = 0;
    let mut result: Vec<char> = Vec::<char>::new();
    let max_len = if len1 > len2 { len1 } else { len2 };
    let mut i = 0;
    while i < max_len
        invariant
            carry <= 1,
            ValidBitString(result@),
        decreases max_len - i
    {
        let b1 = if i < len1 { s1[len1 - 1 - i] } else { '0' };
        let b2 = if i < len2 { s2[len2 - 1 - i] } else { '0' };
        let (bit, new_carry) = add_bits(b1, b2, carry);
        result.push(bit);
        carry = new_carry;
        i += 1;
    }
    if carry == 1 {
        result.push('1');
    }
    result.reverse();
    result
}
// </vc-code>

fn main() {}
}