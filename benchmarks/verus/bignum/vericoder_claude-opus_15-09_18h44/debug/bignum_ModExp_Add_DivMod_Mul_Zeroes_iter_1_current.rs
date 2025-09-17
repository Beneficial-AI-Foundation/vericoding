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
spec fn carry_value(a: char, b: char, carry: u8) -> (u8, char) {
    let sum = (if a == '1' { 1u8 } else { 0u8 }) + (if b == '1' { 1u8 } else { 0u8 }) + carry;
    (sum / 2, if sum % 2 == 1 { '1' } else { '0' })
}

fn add_binary_strings(a: &[char], b: &[char]) -> Vec<char>
    requires
        ValidBitString(a@),
        ValidBitString(b@),
    ensures
        ValidBitString(result@),
{
    let mut result = Vec::<char>::new();
    let mut carry = 0u8;
    let mut i = 0;
    let max_len = if a.len() > b.len() { a.len() } else { b.len() };
    
    while i < max_len
        invariant
            carry <= 1,
            i <= max_len,
            ValidBitString(result@),
    {
        let a_bit = if i < a.len() { a[a.len() - 1 - i] } else { '0' };
        let b_bit = if i < b.len() { b[b.len() - 1 - i] } else { '0' };
        
        let (new_carry, sum_bit) = carry_value(a_bit, b_bit, carry);
        result.push(sum_bit);
        carry = new_carry;
        i = i + 1;
    }
    
    if carry == 1 {
        result.push('1');
    }
    
    // Reverse the result
    let mut reversed = Vec::<char>::new();
    let mut j = result.len();
    while j > 0
        invariant
            j <= result.len(),
            ValidBitString(reversed@),
            ValidBitString(result@),
    {
        j = j - 1;
        reversed.push(result[j]);
    }
    
    reversed
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_DivMod_Mul_Zeroes(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
    add_binary_strings(a, b)
}
// </vc-code>

fn main() {}
}

