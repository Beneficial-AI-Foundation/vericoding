
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
spec fn bit_to_nat(c: char) -> nat { if c == '1' { 1 } else { 0 } }
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
    let mut d_val: nat = 0;
    let mut i: int = 0;
    while i < divisor.len() as int
        invariant 0 <= i && i <= divisor.len() as int,
        decreases divisor.len() as int - i
    {
        d_val = 2 * d_val + (if divisor[i as usize] == '1' { 1 } else { 0 });
        i += 1;
    }

    let mut q = Vec::<char>::new();
    let mut r_val: nat = 0;
    let mut j: int = 0;
    while j < dividend.len() as int
        invariant 0 <= j && j <= dividend.len() as int,
        decreases dividend.len() as int - j
    {
        r_val = 2 * r_val + (if dividend[j as usize] == '1' { 1 } else { 0 });
        if r_val >= d_val {
            q.push('1');
            r_val = r_val - d_val;
        } else {
            q.push('0');
        }
        j += 1;
    }

    let mut rem = Vec::<char>::new();
    if r_val != 0 {
        let mut bits_rev = Vec::<char>::new();
        let mut temp: nat = r_val;
        while temp > 0
            invariant temp >= 0,
            decreases temp
        {
            let bit = if temp % 2 == 1 { '1' } else { '0' };
            bits_rev.push(bit);
            temp = temp / 2;
        }
        let mut k: int = bits_rev.len() as int - 1;
        while k >= 0
            invariant -1 <= k && k < bits_rev.len() as int,
            decreases k + 1
        {
            rem.push(bits_rev[k as usize]);
            k -= 1;
        }
    }

    return (q, rem);
}
// </vc-code>

fn main() {}
}


