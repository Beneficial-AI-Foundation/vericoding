
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
/* helper modified by LLM (iteration 5): convert bit char to nat */
spec fn bit_to_nat(c: char) -> nat { if c == '1' { 1nat } else { 0nat } }

/* helper modified by LLM (iteration 5): Str2Int on prefix when appending bit */
proof fn Str2Int_push_bit(s: Seq<char>, n: int)
    requires 0 <= n && n < s.len() as int,
    ensures Str2Int(s.subrange(0, n+1)) == 2 * Str2Int(s.subrange(0,n)) + (if s.index(n) == '1' { 1nat } else { 0nat })
{
}

// </vc-helpers>

// <vc-spec>
exec fn DivMod(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute divisor and dividend values as nat, compute quotient and remainder, then convert to bit vectors */
    let mut i: int = 0;
    let mut d_val: nat = 0;
    while i < divisor.len() as int
        invariant
            0 <= i && i <= divisor.len() as int,
            d_val == Str2Int(divisor@.subrange(0, i)),
        decreases
            divisor.len() as int - i
    {
        d_val = 2 * d_val + (if divisor[i as usize] == '1' { 1nat } else { 0nat });
        i += 1;
    }

    let mut j: int = 0;
    let mut dvd_val: nat = 0;
    while j < dividend.len() as int
        invariant
            0 <= j && j <= dividend.len() as int,
            dvd_val == Str2Int(dividend@.subrange(0, j)),
        decreases
            dividend.len() as int - j
    {
        dvd_val = 2 * dvd_val + (if dividend[j as usize] == '1' { 1nat } else { 0nat });
        j += 1;
    }

    let q_n: nat = dvd_val / d_val;
    let r_n: nat = dvd_val % d_val;

    let mut q = Vec::<char>::new();
    if q_n != 0 {
        let mut bits_rev = Vec::<char>::new();
        let mut temp: nat = q_n;
        while temp > 0
            invariant
                temp >= 0,
            decreases
                temp
        {
            let bit = if temp % 2 == 1nat { '1' } else { '0' };
            bits_rev.push(bit);
            temp = temp / 2;
        }
        let mut idx: int = bits_rev.len() as int;
        while idx > 0
            invariant
                0 <= idx && idx <= bits_rev.len() as int,
            decreases
                idx
        {
            idx -= 1;
            q.push(bits_rev[idx as usize]);
        }
    }

    let mut rem = Vec::<char>::new();
    if r_n != 0 {
        let mut bits_rev = Vec::<char>::new();
        let mut temp: nat = r_n;
        while temp > 0
            invariant
                temp >= 0,
            decreases
                temp
        {
            let bit = if temp % 2 == 1nat { '1' } else { '0' };
            bits_rev.push(bit);
            temp = temp / 2;
        }
        let mut idx: int = bits_rev.len() as int;
        while idx > 0
            invariant
                0 <= idx && idx <= bits_rev.len() as int,
            decreases
                idx
        {
            idx -= 1;
            rem.push(bits_rev[idx as usize]);
        }
    }

    return (q, rem);
}

// </vc-code>

fn main() {}
}


