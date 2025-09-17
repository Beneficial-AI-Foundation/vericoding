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
/* helper modified by LLM (iteration 5): convert nat to bit vector */
fn nat_to_bits(n: nat) -> Vec<char>
    ensures
        ValidBitString(result@),
        Str2Int(result@) == n,
{
    let mut m = n;
    let mut rev: Vec<char> = Vec::new();
    if m == 0 {
        return Vec::new();
    }
    while m > 0
        invariant
            true,
        decreases m
    {
        let bit: nat = m % 2;
        if bit == 1 { rev.push('1'); } else { rev.push('0'); }
        m = m / 2;
    }
    let mut res: Vec<char> = Vec::new();
    let mut j: usize = rev.len();
    while j > 0
        invariant
            j <= rev.len(),
        decreases j
    {
        j -= 1;
        res.push(rev[j]);
    }
    res
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
    /* code modified by LLM (iteration 5): compute numeric values then convert to bit vectors */
    let mut dv: nat = 0;
    let mut i: usize = 0;
    while i < dividend.len()
        invariant
            i <= dividend.len(),
            dv == Str2Int(dividend@.subrange(0, i as int)),
        decreases dividend.len() - i
    {
        let bit: nat = if dividend[i] == '1' { 1 } else { 0 };
        dv = 2 * dv + bit;
        i += 1;
        proof {
            assert(dv == Str2Int(dividend@.subrange(0, i as int)));
        }
    }

    let mut dvs: nat = 0;
    let mut j: usize = 0;
    while j < divisor.len()
        invariant
            j <= divisor.len(),
            dvs == Str2Int(divisor@.subrange(0, j as int)),
        decreases divisor.len() - j
    {
        let bit: nat = if divisor[j] == '1' { 1 } else { 0 };
        dvs = 2 * dvs + bit;
        j += 1;
        proof {
            assert(dvs == Str2Int(divisor@.subrange(0, j as int)));
        }
    }

    let qn: nat = dv / dvs;
    let rn: nat = dv % dvs;
    let q = nat_to_bits(qn);
    let r = nat_to_bits(rn);
    (q, r)
}

// </vc-code>

fn main() {}
}

