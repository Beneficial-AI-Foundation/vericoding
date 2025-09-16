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
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
/* helper modified by LLM (iteration 9): Fix integer literal suffixes */
fn char_to_bit(c: char) -> int
    requires c == '0' || c == '1'
{
    if c == '1' { 1 } else { 0 }
}

fn bit_to_char(b: int) -> char
    requires b == 0 || b == 1
{
    if b == 1 { '1' } else { '0' }
}
// </vc-helpers>

// <vc-spec>
exec fn Mul_Add_NormalizeBitString(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 9): Fix integer literal suffixes */
{
    let mut result = Vec::with_capacity(s1.len() + s2.len());
    
    for _ in 0..(s1.len() + s2.len()) {
        result.push('0');
    }
    
    let mut carry = 0;
    
    for i in 0..s1.len() {
        let mut temp_carry = 0;
        for j in 0..s2.len() {
            let bit1 = char_to_bit(s1[i]);
            let bit2 = char_to_bit(s2[j]);
            let product = bit1 * bit2 + temp_carry;
            let current_bit = char_to_bit(result[i + j]);
            let sum = current_bit + product + carry;
            
            result[i + j] = bit_to_char(sum & 1);
            carry = if sum >= 2 { 1 } else { 0 };
            temp_carry = if product >= 2 { 1 } else { 0 };
        }
        if carry > 0 {
            result[i + s2.len()] = bit_to_char(carry & 1);
            carry = if carry >= 2 { 1 } else { 0 };
        }
    }
    
    let mut new_len = result.len();
    while new_len > 0 && result[new_len - 1] == '0' {
        new_len -= 1;
    }
    
    if new_len == 0 {
        result.truncate(1);
        result[0] = '0';
    } else {
        result.truncate(new_len);
    }
    
    result
}
// </vc-code>

fn main() {}
}
