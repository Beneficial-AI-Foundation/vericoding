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
/* helper modified by LLM (iteration 4): fixed nat literal types in returns */
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

exec fn binary_add(a: &[char], b: &[char]) -> (result: Vec<char>)
    requires ValidBitString(a@), ValidBitString(b@)
    ensures ValidBitString(result@)
{
    let mut res = Vec::new();
    let mut carry = 0nat;
    let mut i = 0;
    let max_len = if a.len() > b.len() { a.len() } else { b.len() };
    
    while i < max_len || carry > 0
        invariant
            i <= max_len,
            carry == 0 || carry == 1,
            ValidBitString(res@)
    {
        let a_bit = if i < a.len() && a.len() > i { char_to_digit(a[a.len() - 1 - i]) } else { 0nat };
        let b_bit = if i < b.len() && b.len() > i { char_to_digit(b[b.len() - 1 - i]) } else { 0nat };
        let sum = a_bit + b_bit + carry;
        let bit = sum % 2;
        carry = sum / 2;
        res.push(digit_to_char(bit));
        i = i + 1;
    }
    
    let mut result = Vec::new();
    let mut j = 0;
    while j < res.len()
        invariant
            j <= res.len(),
            ValidBitString(result@)
    {
        result.push(res[res.len() - 1 - j]);
        j = j + 1;
    }
    
    if result.len() == 0 {
        result.push('0');
    }
    
    result
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_DivMod_ModExpPow2_Zeroes(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): implementation remains the same */
    let result = binary_add(a, b);
    result
}
// </vc-code>

fn main() {}
}

