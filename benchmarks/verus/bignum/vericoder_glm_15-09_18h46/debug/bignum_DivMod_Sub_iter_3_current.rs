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
/* helper modified by LLM (iteration 3): fixed type annotations and integer literals */
spec fn GreaterEqual(s1: Seq<char>, s2: Seq<char>) -> bool {
    Str2Int(s1) >= Str2Int(s2)
}

exec fn AppendBit(s: &Vec<char>, bit: char) -> (res: Vec<char>)
    requires
        ValidBitString(s@),
        bit == '0' || bit == '1',
    ensures
        ValidBitString(res@),
        Str2Int(res@) == 2 * Str2Int(s@) + (if bit=='1' { 1int } else { 0int }),
{
    let mut res = s.clone();
    res.push(bit);
    res
}

exec fn Subtract(s1: &Vec<char>, s2: &Vec<char>) -> (res: Vec<char>)
    requires
        ValidBitString(s1@),
        ValidBitString(s2@),
        Str2Int(s1@) >= Str2Int(s2@),
    ensures
        ValidBitString(res@),
        Str2Int(res@) == Str2Int(s1@) - Str2Int(s2@),
{
    let mut s1_rev: Vec<char> = s1.iter().cloned().rev().collect();
    let mut s2_rev: Vec<char> = s2.iter().cloned().rev().collect();
    let len = s1_rev.len().max(s2_rev.len());
    let mut borrow = 0int;
    let mut res_rev: Vec<char> = Vec::new();

    for i in 0..len {
        let a = if i < s1_rev.len() { s1_rev[i] } else { '0' };
        let b = if i < s2_rev.len() { s2_rev[i] } else { '0' };
        let a_digit = if a == '1' { 1int } else { 0int };
        let b_digit = if b == '1' { 1int } else { 0int };
        let diff = a_digit - b_digit - borrow;
        borrow = if diff < 0 { 1int } else { 0int };
        let digit = if diff < 0 { diff + 2int } else { diff };
        res_rev.push(if digit == 1 { '1' } else { '0' });
    }

    let mut res: Vec<char> = res_rev.iter().cloned().rev().collect();

    while res.len() > 1 && res[0] == '0' {
        res.remove(0);
    }
    if res.is_empty() {
        res.push('0');
    }

    res
}

exec fn compare_bit_strings(s1: &Vec<char>, s2: &Vec<char>) -> (res: int)
    requires
        ValidBitString(s1@),
        ValidBitString(s2@),
    ensures
        (res == 0int && Str2Int(s1@) == Str2Int(s2@)) ||
        (res == 1int && Str2Int(s1@) > Str2Int(s2@)) ||
        (res == -1int && Str2Int(s1@) < Str2Int(s2@)),
{
    if s1.len() > s2.len() {
        1int
    } else if s1.len() < s2.len() {
        -1int
    } else {
        let mut i = 0;
        while i < s1.len()
            invariant 0 <= i <= s1.len()
            decreases s1.len() - i
        {
            if s1[i] != s2[i] {
                if s1[i] == '1' {
                    return 1int;
                } else {
                    return -1int;
                }
            }
            i += 1;
        }
        0int
    }
}
// </vc-helpers>

// <vc-spec>
exec fn DivMod_Sub(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fixed type conversions and comparisons */
    let mut quotient: Vec<char> = Vec::new();
    let mut remainder: Vec<char> = Vec::new();

    for i in 0..dividend.len() {
        let bit = dividend[i];
        remainder = AppendBit(&remainder, bit);

        let cmp = compare_bit_strings(&remainder, &Vec::from(divisor));
        if cmp >= 0int {
            remainder = Subtract(&remainder, &Vec::from(divisor));
            quotient = AppendBit(&quotient, '1');
        } else {
            quotient = AppendBit(&quotient, '0');
        }
    }

    (quotient, remainder)
}
// </vc-code>

fn main() {}
}

