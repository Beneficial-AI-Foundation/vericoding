
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
/* helper modified by LLM (iteration 7): convert bit char to nat */
spec fn bit_to_nat(c: char) -> nat { if c == '1' { 1nat } else { 0nat } }
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
    /* code modified by LLM (iteration 7): use fixed-bound for loops to avoid while decreases */
    let mut d_val: u128 = 0u128;
    for k in 0..divisor.len() {
        d_val = d_val * 2u128 + (if divisor[k] == '1' { 1u128 } else { 0u128 });
    }

    let mut dvd_val: u128 = 0u128;
    for k in 0..dividend.len() {
        dvd_val = dvd_val * 2u128 + (if dividend[k] == '1' { 1u128 } else { 0u128 });
    }

    let q_n: u128 = if d_val == 0u128 { 0u128 } else { dvd_val / d_val };
    let r_n: u128 = if d_val == 0u128 { dvd_val } else { dvd_val % d_val };

    let mut q = Vec::<char>::new();
    if q_n != 0u128 {
        let mut seen = false;
        for shift in (0..128).rev() {
            let bit_is_one = ((q_n >> shift) & 1u128) == 1u128;
            if bit_is_one {
                q.push('1');
                seen = true;
            } else if seen {
                q.push('0');
            }
        }
    }

    let mut rem = Vec::<char>::new();
    if r_n != 0u128 {
        let mut seen = false;
        for shift in (0..128).rev() {
            let bit_is_one = ((r_n >> shift) & 1u128) == 1u128;
            if bit_is_one {
                rem.push('1');
                seen = true;
            } else if seen {
                rem.push('0');
            }
        }
    }

    return (q, rem);
}

// </vc-code>

fn main() {}
}


