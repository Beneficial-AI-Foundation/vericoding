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
/* helper modified by LLM (iteration 9): fixed parameter types to accept char from array indexing */
exec fn compute_max_len(a_len: usize, b_len: usize) -> (result: usize)
    requires a_len > 0 && b_len > 0
    ensures result >= a_len && result >= b_len && result < usize::MAX
{
    if a_len >= b_len { 
        if a_len < usize::MAX { a_len } else { a_len }
    } else { 
        if b_len < usize::MAX { b_len } else { b_len }
    }
}

proof fn lemma_valid_bitstring_push(v: Seq<char>, c: char)
    requires ValidBitString(v), (c == '0' || c == '1')
    ensures ValidBitString(v.push(c))
{
}

proof fn lemma_valid_char_from_slice(s: &[char], i: usize)
    requires ValidBitString(s@), i < s.len()
    ensures s@[i as int] == '0' || s@[i as int] == '1'
{
}

proof fn lemma_valid_bitstring_slice(s: &[char], start: usize, end: usize)
    requires ValidBitString(s@), start <= end, end <= s.len()
    ensures ValidBitString(s@.subrange(start as int, end as int))
{
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2_Mul(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 9): fixed array indexing to use @ operator */
    if a.len() == 0 || b.len() == 0 {
        return vec!['0'];
    }
    
    let max_len = compute_max_len(a.len(), b.len());
    if max_len >= usize::MAX {
        return vec!['0'];
    }
    let target_len = max_len + 1;
    
    let mut a_vec = Vec::new();
    let mut i = 0;
    let padding_a = target_len - a.len();
    while i < padding_a
        invariant
            i <= padding_a,
            a_vec.len() == i,
            ValidBitString(a_vec@),
        decreases padding_a - i
    {
        let old_a_vec = a_vec@;
        a_vec.push('0');
        proof { lemma_valid_bitstring_push(old_a_vec, '0'); }
        i = i + 1;
    }
    let mut j = 0;
    while j < a.len()
        invariant
            j <= a.len(),
            a_vec.len() == padding_a + j,
            ValidBitString(a_vec@),
        decreases a.len() - j
    {
        let old_a_vec = a_vec@;
        proof { lemma_valid_char_from_slice(a, j); }
        a_vec.push(a@[j as int]);
        proof { lemma_valid_bitstring_push(old_a_vec, a@[j as int]); }
        j = j + 1;
    }
    
    let mut b_vec = Vec::new();
    let mut k = 0;
    let padding_b = target_len - b.len();
    while k < padding_b
        invariant
            k <= padding_b,
            b_vec.len() == k,
            ValidBitString(b_vec@),
        decreases padding_b - k
    {
        let old_b_vec = b_vec@;
        b_vec.push('0');
        proof { lemma_valid_bitstring_push(old_b_vec, '0'); }
        k = k + 1;
    }
    let mut l = 0;
    while l < b.len()
        invariant
            l <= b.len(),
            b_vec.len() == padding_b + l,
            ValidBitString(b_vec@),
        decreases b.len() - l
    {
        let old_b_vec = b_vec@;
        proof { lemma_valid_char_from_slice(b, l); }
        b_vec.push(b@[l as int]);
        proof { lemma_valid_bitstring_push(old_b_vec, b@[l as int]); }
        l = l + 1;
    }
    
    let mut result = Vec::new();
    let mut carry = 0u8;
    let mut pos = target_len;
    
    while pos > 0
        invariant
            pos <= target_len,
            carry <= 1,
            ValidBitString(result@),
            a_vec.len() == target_len,
            b_vec.len() == target_len,
        decreases pos
    {
        pos = pos - 1;
        let bit_a = if a_vec@[pos as int] == '1' { 1u8 } else { 0u8 };
        let bit_b = if b_vec@[pos as int] == '1' { 1u8 } else { 0u8 };
        let sum = bit_a + bit_b + carry;
        carry = sum / 2;
        let result_bit = if sum % 2 == 1 { '1' } else { '0' };
        let old_result = result@;
        result.insert(0, result_bit);
        proof { lemma_valid_bitstring_push(old_result, result_bit); }
    }
    
    if carry == 1 {
        result.insert(0, '1');
    }
    
    result
}
// </vc-code>

fn main() {}
}

