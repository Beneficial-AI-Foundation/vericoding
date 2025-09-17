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
spec fn is_bit(c: char) -> bool { c == '0' || c == '1' }
spec fn bit(c: char) -> nat { if c == '1' { 1nat } else { 0nat } }
proof fn lemma_valid_bitstring_singleton(c: char)
    requires
        is_bit(c),
    ensures
        ValidBitString(seq![c]),
{
}
proof fn lemma_valid_bitstring_push(s: Seq<char>, c: char)
    requires
        ValidBitString(s),
        is_bit(c),
    ensures
        ValidBitString(s + seq![c]),
{
}
// </vc-helpers>

// <vc-spec>
exec fn Sub(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@), Str2Int(s1@) >= Str2Int(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) - Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    let mut i1: isize = s1.len() as isize;
    let mut i2: isize = s2.len() as isize;
    let mut borrow: i32 = 0;
    let mut res_rev: Vec<char> = Vec::new();
    while i1 > 0 || i2 > 0
        invariant
            0 <= borrow && borrow <= 1,
            ValidBitString(res_rev@),
            0 <= i1 && i1 <= s1.len() as isize,
            0 <= i2 && i2 <= s2.len() as isize,
        decreases
            ((i1 as int) + (i2 as int)) as nat
    {
        let c1 = if i1 > 0 { s1[(i1 - 1) as usize] } else { '0' };
        let c2 = if i2 > 0 { s2[(i2 - 1) as usize] } else { '0' };
        let b1: i32 = if c1 == '1' { 1 } else { 0 };
        let b2: i32 = if c2 == '1' { 1 } else { 0 };
        let mut val: i32 = b1 - b2 - borrow;
        if val < 0 {
            val += 2;
            borrow = 1;
        } else {
            borrow = 0;
        }
        let ch = if val == 1 { '1' } else { '0' };
        res_rev.push(ch);
        if i1 > 0 { i1 -= 1; }
        if i2 > 0 { i2 -= 1; }
    }

    let mut res: Vec<char> = Vec::new();
    let mut j: isize = res_rev.len() as isize;
    while j > 0
        invariant
            ValidBitString(res@),
            0 <= j && j <= res_rev.len() as isize,
        decreases
            j as nat
    {
        res.push(res_rev[(j - 1) as usize]);
        j -= 1;
    }

    // Trim leading zeros while keeping at least one digit
    let mut k: usize = 0;
    while k < res.len() && res[k] == '0'
        invariant
            k <= res.len(),
        decreases
            (res.len() - k) as nat
    {
        k += 1;
    }
    if k == res.len() {
        let mut zero_vec: Vec<char> = Vec::new();
        zero_vec.push('0');
        return zero_vec;
    }
    if k > 0 {
        let mut trimmed: Vec<char> = Vec::new();
        let mut t: usize = k;
        while t < res.len()
            invariant
                ValidBitString(trimmed@),
                t <= res.len(),
            decreases
                (res.len() - t) as nat
        {
            trimmed.push(res[t]);
            t += 1;
        }
        return trimmed;
    }
    res
}
// </vc-code>

fn main() {}
}


