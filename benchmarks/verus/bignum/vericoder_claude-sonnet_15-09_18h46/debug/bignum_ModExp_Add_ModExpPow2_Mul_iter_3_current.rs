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
/* helper modified by LLM (iteration 3): removed complex spec functions and added simpler executable helpers */
exec fn compute_max_len(a_len: usize, b_len: usize) -> (result: usize)
    ensures result >= a_len && result >= b_len
{
    if a_len >= b_len { a_len } else { b_len }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2_Mul(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fixed compilation error by removing spec mode call */
    let target_len = compute_max_len(a.len(), b.len()) + 1;
    
    let mut a_vec = Vec::new();
    let mut i = 0;
    while i < target_len - a.len()
        invariant
            i <= target_len - a.len(),
            a_vec.len() == i,
            ValidBitString(a_vec@)
    {
        a_vec.push('0');
        i = i + 1;
    }
    let mut j = 0;
    while j < a.len()
        invariant
            j <= a.len(),
            a_vec.len() == (target_len - a.len()) + j,
            ValidBitString(a_vec@)
    {
        a_vec.push(a[j]);
        j = j + 1;
    }
    
    let mut b_vec = Vec::new();
    let mut k = 0;
    while k < target_len - b.len()
        invariant
            k <= target_len - b.len(),
            b_vec.len() == k,
            ValidBitString(b_vec@)
    {
        b_vec.push('0');
        k = k + 1;
    }
    let mut l = 0;
    while l < b.len()
        invariant
            l <= b.len(),
            b_vec.len() == (target_len - b.len()) + l,
            ValidBitString(b_vec@)
    {
        b_vec.push(b[l]);
        l = l + 1;
    }
    
    let mut result = Vec::new();
    let mut carry = 0u8;
    let mut pos = target_len;
    
    while pos > 0
        invariant
            pos <= target_len,
            carry <= 1,
            ValidBitString(result@)
    {
        pos = pos - 1;
        let bit_a = if a_vec[pos] == '1' { 1u8 } else { 0u8 };
        let bit_b = if b_vec[pos] == '1' { 1u8 } else { 0u8 };
        let sum = bit_a + bit_b + carry;
        carry = sum / 2;
        let result_bit = if sum % 2 == 1 { '1' } else { '0' };
        result.insert(0, result_bit);
    }
    
    if carry == 1 {
        result.insert(0, '1');
    }
    
    result
}
// </vc-code>

fn main() {}
}

