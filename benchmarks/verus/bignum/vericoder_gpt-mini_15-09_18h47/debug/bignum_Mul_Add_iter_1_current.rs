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
spec fn pow2(k: nat) -> nat
    decreases k
{
    if k == 0 { 1 } else { 2 * pow2(k - 1) }
}

spec fn char_to_nat(c: char) -> nat
{
    if c == '1' { 1 } else { 0 }
}
// </vc-helpers>

// <vc-spec>
exec fn Mul_Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    let n1 = s1.len() as int;
    let mut i1: int = 0;
    let mut v1: nat = 0;
    while i1 < n1
        invariant
            0 <= i1 && i1 <= n1,
            v1 == Str2Int(s1@.subrange(0, i1)),
        decreases n1 - i1
    {
        let b = if s1@.index(i1) == '1' { 1 } else { 0 };
        v1 = 2 * v1 + b;
        i1 += 1;
    }

    let n2 = s2.len() as int;
    let mut i2: int = 0;
    let mut v2: nat = 0;
    while i2 < n2
        invariant
            0 <= i2 && i2 <= n2,
            v2 == Str2Int(s2@.subrange(0, i2)),
        decreases n2 - i2
    {
        let b = if s2@.index(i2) == '1' { 1 } else { 0 };
        v2 = 2 * v2 + b;
        i2 += 1;
    }

    let mut p: nat = v1 * v2;
    let p0 = p;
    let mut res = Vec::<char>::new();
    if p == 0 {
        res.push('0');
    } else {
        let mut k: nat = 0;
        while p > 0
            invariant
                Str2Int(res@) + pow2(k) * p == p0,
            decreases p
        {
            if p % 2 == 1 {
                res.push('1');
            } else {
                res.push('0');
            }
            p = p / 2;
            k = k + 1;
        }
    }
    res
}
// </vc-code>

fn main() {}
}
