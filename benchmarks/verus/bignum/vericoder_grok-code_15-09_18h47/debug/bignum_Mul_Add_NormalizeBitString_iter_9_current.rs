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
/* helper modified by LLM (iteration 9): replaced char::from with direct char literals to avoid unsupported conversion */
exec fn add_binary_strings(s1: &[char], s2: &[char]) -> (res: Vec<char>)
    requires
        ValidBitString(s1@),
        ValidBitString(s2@),
    ensures
        ValidBitString(res@),
        Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@),
{
    let mut res_vec: Vec<char> = Vec::new();
    let mut i: usize = if s1.len() > 0 { s1.len() - 1 } else { usize::MAX };
    let mut j: usize = if s2.len() > 0 { s2.len() - 1 } else { usize::MAX };
    let mut carry: u32 = 0;
    while ((i < usize::MAX || j < usize::MAX || carry > 0) && i.wrapping_add(1) <= usize::MAX && j.wrapping_add(1) <= usize::MAX)
        invariant
            ValidBitString(s1@),
            ValidBitString(s2@),
        decreases
            (if i < usize::MAX { i as nat } else { s1.len() as nat }) + (if j < usize::MAX { j as nat } else { s2.len() as nat }) + (if carry > 0 { 1nat } else { 0nat }),
    {
        let bit1: u32 = if i < usize::MAX { (s1[i] as u32) - ('0' as u32) } else { 0 };
        let bit2: u32 = if j < usize::MAX { (s2[j] as u32) - ('0' as u32) } else { 0 };
        let sum: u32 = bit1 + bit2 + carry;
        res_vec.push(if sum % 2 == 0 { '0' } else { '1' });
        carry = sum / 2;
        if i < usize::MAX { i = i.wrapping_sub(1); }
        if j < usize::MAX { j = j.wrapping_sub(1); }
    }
    let mut final_vec: Vec<char> = Vec::new();
    while res_vec.len() > 0
        invariant
            res_vec.len() as int >= 0,
        decreases
            res_vec.len() as nat,
    {
        final_vec.push(res_vec.pop().unwrap());
    }
    final_vec
}

/* helper modified by LLM (iteration 9): copied unchanged as no issues */
exec fn shift_binary(s: &[char], m: usize) -> (res: Vec<char>)
    requires
        ValidBitString(s@),
    ensures
        ValidBitString(res@),
        Str2Int(res@) == Str2Int(s@) * vstd::arithmetic::power2::pow2(m as nat),
{
    let mut res_vec: Vec<char> = Vec::new();
    let s_seq = s@;
    let mut idx = 0;
    while idx < s.len()
        invariant
            0 <= idx <= s.len(),
            res_vec.len() == idx,
        decreases
            s.len() - idx,
    {
        res_vec.push(s[idx]);
        idx += 1;
    }
    let mut shift_count = 0;
    while shift_count < m
        invariant
            0 <= shift_count <= m,
            res_vec.len() == s.len() + shift_count,
        decreases
            m - shift_count,
    {
        res_vec.push('0');
        shift_count += 1;
    }
    res_vec
}
// </vc-helpers>

// <vc-spec>
exec fn Mul_Add_NormalizeBitString(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 9): copied unchanged as fixes are in helpers */
{
    /* code modified by LLM (iteration 8): implemented binary multiplication using shift and add */
    let mut result: Vec<char> = Vec::new();
    let mut idx = 0;
    while idx < s2.len()
        invariant
            ValidBitString(s1@),
            ValidBitString(s2@),
            ValidBitString(result@),
            0 <= idx <= s2.len(),
        decreases
            s2.len() - idx,
    {
        if s2[idx] == '1' {
            let shift_amount = s2.len() - 1 - idx;
            let shifted_s1 = shift_binary(s1, shift_amount);
            result = add_binary_strings(&result, &shifted_s1);
        }
        idx += 1;
    }
    if result.len() == 0 {
        result.push('0');
    }
    result
}
// </vc-code>

fn main() {}
}
