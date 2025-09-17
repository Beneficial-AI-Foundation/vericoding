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
/* helper modified by LLM (iteration 4): added decreases clause to loop */
proof fn lemma_str2int_append_zero(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s.push('0')) == 2 * Str2Int(s)
{
}

proof fn lemma_str2int_append_one(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s.push('1')) == 2 * Str2Int(s) + 1
{
}

proof fn lemma_valid_bit_string_push(s: Seq<char>, c: char)
    requires ValidBitString(s), c == '0' || c == '1'
    ensures ValidBitString(s.push(c))
{
}

exec fn copy_slice_to_vec(s: &[char]) -> (res: Vec<char>)
    requires ValidBitString(s@)
    ensures ValidBitString(res@), res@ == s@
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
        i += 1;
    }
    result
}

exec fn add_bit_strings(a: &[char], b: &[char]) -> (res: Vec<char>)
    requires ValidBitString(a@), ValidBitString(b@)
    ensures ValidBitString(res@)
{
    let mut result = Vec::new();
    let mut carry = 0u8;
    let max_len = if a.len() > b.len() { a.len() } else { b.len() };
    
    let mut i = 0;
    while i < max_len || carry > 0
        invariant
            ValidBitString(result@),
            carry <= 1,
            i <= max_len
        decreases (max_len + 1) - i
    {
        let a_bit = if i < a.len() && a.len() > i { if a[a.len() - 1 - i] == '1' { 1u8 } else { 0u8 } } else { 0u8 };
        let b_bit = if i < b.len() && b.len() > i { if b[b.len() - 1 - i] == '1' { 1u8 } else { 0u8 } } else { 0u8 };
        
        let sum = a_bit + b_bit + carry;
        let digit = if sum % 2 == 1 { '1' } else { '0' };
        carry = sum / 2;
        
        result.push(digit);
        i += 1;
    }
    
    // Build reversed result manually instead of using reverse()
    let mut final_result = Vec::new();
    let mut j = result.len();
    while j > 0
        invariant ValidBitString(final_result@)
        decreases j
    {
        j -= 1;
        final_result.push(result[j]);
    }
    
    if final_result.len() == 0 {
        final_result.push('0');
    }
    final_result
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_DivMod_ModExpPow2_Zeroes(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): fixed function implementation to add decreases clause to all loops */
{
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

