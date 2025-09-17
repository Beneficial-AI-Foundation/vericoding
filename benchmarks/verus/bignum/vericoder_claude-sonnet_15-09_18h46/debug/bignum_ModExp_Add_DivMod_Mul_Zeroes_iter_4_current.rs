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
/* helper modified by LLM (iteration 4): Fixed type errors by using nat literals with explicit casting */
exec fn char_to_digit(c: char) -> (result: nat)
    requires c == '0' || c == '1'
    ensures result == 0 || result == 1,
            c == '0' ==> result == 0,
            c == '1' ==> result == 1
{
    if c == '1' { 1nat } else { 0nat }
}

exec fn digit_to_char(d: nat) -> (result: char)
    requires d == 0 || d == 1
    ensures result == '0' || result == '1',
            d == 0 ==> result == '0',
            d == 1 ==> result == '1'
{
    if d == 1nat { '1' } else { '0' }
}

exec fn add_bit_strings(a: &[char], b: &[char]) -> (result: Vec<char>)
    requires ValidBitString(a@), ValidBitString(b@)
    ensures ValidBitString(result@)
{
    let mut res = Vec::new();
    let mut carry = 0nat;
    let mut i = 0;
    let max_len = if a.len() > b.len() { a.len() } else { b.len() };
    
    while i < max_len || carry > 0
        invariant
            ValidBitString(res@),
            carry == 0 || carry == 1,
            i <= max_len
    {
        let a_bit = if i < a.len() { char_to_digit(a[a.len() - 1 - i]) } else { 0nat };
        let b_bit = if i < b.len() { char_to_digit(b[b.len() - 1 - i]) } else { 0nat };
        let sum = a_bit + b_bit + carry;
        res.push(digit_to_char(sum % 2));
        carry = sum / 2;
        i = i + 1;
    }
    
    res.reverse();
    if res.len() == 0 {
        res.push('0');
    }
    res
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_DivMod_Mul_Zeroes(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Fixed type consistency for empty vector handling */
    if a.len() == 0 && b.len() == 0 {
        let mut result = Vec::new();
        result.push('0');
        return result;
    }
    
    if a.len() == 0 {
        return b.to_vec();
    }
    
    if b.len() == 0 {
        return a.to_vec();
    }
    
    add_bit_strings(a, b)
}
// </vc-code>

fn main() {}
}

