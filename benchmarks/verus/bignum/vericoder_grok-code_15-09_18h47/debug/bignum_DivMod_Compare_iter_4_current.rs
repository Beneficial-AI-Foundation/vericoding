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
/* helper modified by LLM (iteration 4): Fixed sequence indexing from @[i] to .index(i) to resolve compilation errors */
exec fn remove_leading_zeros(v: &Vec<char>) -> Vec<char>
{
    let mut i: usize = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
        decreases v.len() - i
    {
        if v@.index(i) == '1' {
            break;
        }
        i += 1;
    }
    let mut result = Vec::new();
    for j in i..v.len() {
        result.push(v@.index(j));
    }
    result
}
exec fn is_greater_or_equal(v1: &Vec<char>, v2: &Vec<char>) -> bool
{
    let l1 = v1.len();
    let l2 = v2.len();
    if l1 > l2 {
        return true;
    }
    if l1 < l2 {
        return false;
    }
    for i in 0..l1 {
        if v1@.index(i) > v2@.index(i) {
            return true;
        }
        if v1@.index(i) < v2@.index(i) {
            return false;
        }
    }
    true
}
/* helper modified by LLM (iteration 3): Fixed compilation error by manually reversing the vector instead of using .reverse() on mutable Vec */
/* helper modified by LLM (iteration 4): Fixed sequence indexing from @[j] to .index(j) to resolve compilation errors */
exec fn subtract(v1: &Vec<char>, v2: &Vec<char>) -> Vec<char>
    requires
        ValidBitString(v1@),
        ValidBitString(v2@),
        Str2Int(v1@) >= Str2Int(v2@)
{
    let l1 = v1.len();
    let l2 = v2.len();
    let mut v2_padded = Vec::new();
    for _ in 0..(l1 - l2) {
        v2_padded.push('0');
    }
    v2_padded.extend(v2.iter().cloned());
    let mut temp = Vec::<char>::new();
    let mut borrow = 0;
    let mut j = l1;
    while j > 0
        invariant
            0 <= j <= l1,
        decreases j
    {
        j -= 1;
        let d1 = v1@.index(j) as i32 - '0' as i32;
        let d2 = v2_padded@.index(j) as i32 - '0' as i32;
        let mut res = d1 - borrow - d2;
        if res < 0 {
            res += 2;
            borrow = 1;
        } else {
            borrow = 0;
        }
        temp.push((res as i32 + '0' as i32) as u8 as char);
    }
    // Manual reverse to get MSB first
    let temp_len = temp.len();
    let mut result = Vec::<char>::with_capacity(temp_len);
    for i in 0..temp_len {
        result.push(temp@.index(temp_len - 1 - i));
    }
    remove_leading_zeros(&result)
}
// </vc-helpers>

// <vc-spec>
exec fn DivMod_Compare(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Fixed sequence indexing from @[i] to .index(i) to resolve compilation errors */
    let dividend_vec = dividend.to_vec();
    let divisor_vec = divisor.to_vec();
    let dividend_trimmed = remove_leading_zeros(&dividend_vec);
    let divisor_trimmed = remove_leading_zeros(&divisor_vec);
    let mut remainder: Vec<char> = Vec::new();
    let mut quotient: Vec<char> = Vec::new();
    for &c in dividend_trimmed.iter() {
        remainder.push(c);
        if is_greater_or_equal(&remainder, &divisor_trimmed) {
            quotient.push('1');
            remainder = subtract(&remainder, &divisor_trimmed);
        } else {
            quotient.push('0');
        }
    }
    let mut quotient_final = remove_leading_zeros(&quotient);
    if quotient_final.is_empty() {
        quotient_final.push('0');
    }
    let mut remainder_final = remove_leading_zeros(&remainder);
    if remainder_final.is_empty() {
        remainder_final.push('0');
    }
    (quotient_final, remainder_final)
}
// </vc-code>

fn main() {}
}

