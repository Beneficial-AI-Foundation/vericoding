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
/* helper modified by LLM (iteration 10): Added char validity assertions */
exec fn char_to_digit(c: char) -> (result: u32)
    requires c == '0' || c == '1'
    ensures result == 0 || result == 1,
            c == '0' ==> result == 0,
            c == '1' ==> result == 1
{
    if c == '1' { 1 } else { 0 }
}

exec fn digit_to_char(d: u32) -> (result: char)
    requires d == 0 || d == 1
    ensures result == '0' || result == '1',
            d == 0 ==> result == '0',
            d == 1 ==> result == '1'
{
    if d == 1 { '1' } else { '0' }
}

exec fn add_bit_strings(a: &[char], b: &[char]) -> (result: Vec<char>)
    requires ValidBitString(a@), ValidBitString(b@)
    ensures ValidBitString(result@)
{
    let mut temp_res = Vec::new();
    let mut carry = 0u32;
    let mut i = 0;
    let max_len = if a.len() > b.len() { a.len() } else { b.len() };
    
    while i < max_len || carry > 0
        invariant
            ValidBitString(temp_res@),
            carry == 0 || carry == 1,
            i <= max_len,
            ValidBitString(a@),
            ValidBitString(b@)
        decreases (max_len + 1) - i + carry
    {
        let a_bit = if i < a.len() {
            assert(a.len() - 1 - i < a.len());
            assert(ValidBitString(a@));
            assert(a[a.len() - 1 - i] == '0' || a[a.len() - 1 - i] == '1');
            char_to_digit(a[a.len() - 1 - i])
        } else { 0 };
        let b_bit = if i < b.len() {
            assert(b.len() - 1 - i < b.len());
            assert(ValidBitString(b@));
            assert(b[b.len() - 1 - i] == '0' || b[b.len() - 1 - i] == '1');
            char_to_digit(b[b.len() - 1 - i])
        } else { 0 };
        let sum = a_bit + b_bit + carry;
        let result_char = digit_to_char(sum % 2);
        temp_res.push(result_char);
        assert(result_char == '0' || result_char == '1');
        assert(ValidBitString(temp_res@));
        carry = sum / 2;
        i = i + 1;
    }
    
    let mut res = Vec::new();
    let mut j = 0;
    while j < temp_res.len()
        invariant
            ValidBitString(res@),
            j <= temp_res.len(),
            ValidBitString(temp_res@)
        decreases temp_res.len() - j
    {
        let ch = temp_res[temp_res.len() - 1 - j];
        assert(ch == '0' || ch == '1');
        res.push(ch);
        assert(ValidBitString(res@));
        j = j + 1;
    }
    
    if res.len() == 0 {
        res.push('0');
    }
    res
}

exec fn copy_slice_to_vec(s: &[char]) -> (result: Vec<char>)
    requires ValidBitString(s@)
    ensures ValidBitString(result@),
            result@ == s@
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < s.len()
        invariant
            ValidBitString(result@),
            i <= s.len(),
            result@ == s@.subrange(0, i as int)
        decreases s.len() - i
    {
        result.push(s[i]);
        i = i + 1;
    }
    result
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_DivMod_Mul_Zeroes(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): No changes needed in main function body */
    if a.len() == 0 && b.len() == 0 {
        let mut result = Vec::new();
        result.push('0');
        return result;
    }
    
    if a.len() == 0 {
        return copy_slice_to_vec(b);
    }
    
    if b.len() == 0 {
        return copy_slice_to_vec(a);
    }
    
    add_bit_strings(a, b)
}
// </vc-code>

fn main() {}
}

