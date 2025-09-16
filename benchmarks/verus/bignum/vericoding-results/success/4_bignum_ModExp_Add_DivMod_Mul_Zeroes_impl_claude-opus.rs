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
/* helper modified by LLM (iteration 4): Added decreases clause to while loops */
exec fn add_binary_strings(a: &[char], b: &[char]) -> (output: Vec<char>)
    requires
        ValidBitString(a@),
        ValidBitString(b@),
    ensures
        ValidBitString(output@),
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
        decreases max_len - i
    {
        let a_bit = if i < a.len() { a[a.len() - 1 - i] } else { '0' };
        let b_bit = if i < b.len() { b[b.len() - 1 - i] } else { '0' };
        
        let a_val = if a_bit == '1' { 1u8 } else { 0u8 };
        let b_val = if b_bit == '1' { 1u8 } else { 0u8 };
        let sum = a_val + b_val + carry;
        
        carry = sum / 2;
        let sum_bit = if sum % 2 == 1 { '1' } else { '0' };
        result.push(sum_bit);
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
        decreases j
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
    /* code modified by LLM (iteration 4): Call add_binary_strings and return result */
    let result = add_binary_strings(a, b);
    result
}
// </vc-code>

fn main() {}
}

