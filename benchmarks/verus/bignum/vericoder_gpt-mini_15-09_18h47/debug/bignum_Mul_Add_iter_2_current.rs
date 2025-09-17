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
/* helper modified by LLM (iteration 2): power of two */
spec fn pow2(k: nat) -> nat
    decreases k
{
    if k == 0 { 1 } else { 2 * pow2(k - 1) }
}

/* helper modified by LLM (iteration 2): char to nat */
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
    /* code modified by LLM (iteration 2): use runtime counters with tracked ghost counterparts to compute product and build bit-vector */
    let n1_usize: usize = s1.len();
    let tracked n1: int = n1_usize as int;
    let mut i1_usize: usize = 0;
    let mut tracked i1: int = 0;
    let mut v1_u: usize = 0;
    let mut tracked v1: nat = 0;
    while i1_usize < n1_usize
        invariant
            0 <= i1 && i1 <= n1,
            v1 == Str2Int(s1@.subrange(0, i1)),
            i1 == i1_usize as int,
        decreases n1 - i1
    {
        let b_u: usize = if s1[i1_usize] == '1' { 1 } else { 0 };
        let tracked b_t: nat = if s1@.index(i1) == '1' { 1 } else { 0 };
        v1_u = 2 * v1_u + b_u;
        v1 = 2 * v1 + b_t;
        i1_usize += 1;
        i1 += 1;
    }

    let n2_usize: usize = s2.len();
    let tracked n2: int = n2_usize as int;
    let mut i2_usize: usize = 0;
    let mut tracked i2: int = 0;
    let mut v2_u: usize = 0;
    let mut tracked v2: nat = 0;
    while i2_usize < n2_usize
        invariant
            0 <= i2 && i2 <= n2,
            v2 == Str2Int(s2@.subrange(0, i2)),
            i2 == i2_usize as int,
        decreases n2 - i2
    {
        let b_u: usize = if s2[i2_usize] == '1' { 1 } else { 0 };
        let tracked b_t: nat = if s2@.index(i2) == '1' { 1 } else { 0 };
        v2_u = 2 * v2_u + b_u;
        v2 = 2 * v2 + b_t;
        i2_usize += 1;
        i2 += 1;
    }

    let mut p_u: usize = v1_u * v2_u;
    let mut tracked p: nat = v1 * v2;
    let tracked p0: nat = p;
    let mut res = Vec::<char>::new();
    if p_u == 0 {
        res.push('0');
    } else {
        let mut k_u: usize = 0;
        let mut tracked k: nat = 0;
        while p_u > 0
            invariant
                Str2Int(res@) + pow2(k) * p == p0,
                p == p_u as nat,
                k == k_u as nat,
            decreases p
        {
            if p_u % 2 == 1 {
                res.push('1');
            } else {
                res.push('0');
            }
            p_u = p_u / 2;
            p = p / 2;
            k_u += 1;
            k = k + 1;
        }
    }
    res
}
// </vc-code>

fn main() {}
}
