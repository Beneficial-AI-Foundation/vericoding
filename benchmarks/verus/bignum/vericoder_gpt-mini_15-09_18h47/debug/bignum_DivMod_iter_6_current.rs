
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
/* helper modified by LLM (iteration 6): convert bit char to nat */
spec fn bit_to_nat(c: char) -> nat { if c == '1' { 1nat } else { 0nat } }

/* helper modified by LLM (iteration 6): Str2Int on prefix when appending bit */
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
    /* code modified by LLM (iteration 6): use usize/u128 for runtime arithmetic to avoid ghost nat/int */
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
        let mut bits_rev = Vec::<char>::new();
        let mut temp: u128 = q_n;
        while temp > 0u128 {
            let bit = if temp % 2u128 == 1u128 { '1' } else { '0' };
            bits_rev.push(bit);
            temp = temp / 2u128;
        }
        let mut idx: usize = bits_rev.len();
        while idx > 0 {
            idx -= 1;
            q.push(bits_rev[idx]);
        }
    }

    let mut rem = Vec::<char>::new();
    if r_n != 0u128 {
        let mut bits_rev = Vec::<char>::new();
        let mut temp: u128 = r_n;
        while temp > 0u128 {
            let bit = if temp % 2u128 == 1u128 { '1' } else { '0' };
            bits_rev.push(bit);
            temp = temp / 2u128;
        }
        let mut idx: usize = bits_rev.len();
        while idx > 0 {
            idx -= 1;
            rem.push(bits_rev[idx]);
        }
    }

    return (q, rem);
}

// </vc-code>

fn main() {}
}


