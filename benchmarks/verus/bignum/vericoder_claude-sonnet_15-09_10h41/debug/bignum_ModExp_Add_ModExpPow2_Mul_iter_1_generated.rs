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
exec fn char_to_digit(c: char) -> (result: nat)
    requires c == '0' || c == '1'
    ensures result == 0 || result == 1,
            (c == '0') ==> (result == 0),
            (c == '1') ==> (result == 1)
{
    if c == '1' { 1 } else { 0 }
}

exec fn digit_to_char(n: nat) -> (result: char)
    requires n == 0 || n == 1
    ensures result == '0' || result == '1',
            (n == 0) ==> (result == '0'),
            (n == 1) ==> (result == '1')
{
    if n == 1 { '1' } else { '0' }
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
        let a_bit = if i < a.len() { char_to_digit(a[a.len() - 1 - i]) } else { 0 };
        let b_bit = if i < b.len() { char_to_digit(b[b.len() - 1 - i]) } else { 0 };
        let sum = a_bit + b_bit + carry;
        let result_bit = sum % 2;
        carry = sum / 2;
        res.push(digit_to_char(result_bit));
        i += 1;
    }
    
    let mut final_result = Vec::new();
    let mut j = 0;
    while j < res.len()
        invariant
            ValidBitString(final_result@),
            j <= res.len()
    {
        final_result.push(res[res.len() - 1 - j]);
        j += 1;
    }
    
    if final_result.len() == 0 {
        final_result.push('0');
    }
    
    final_result
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2_Mul(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
    add_bit_strings(a, b)
}
// </vc-code>

fn main() {}
}

