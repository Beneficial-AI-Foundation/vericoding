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
spec fn pow2(k: int) -> nat
    requires
        k >= 0,
    decreases k
{
    if k == 0 {
        1
    } else {
        2 * pow2(k - 1)
    }
}

fn rem_to_bits(orig: nat, k: int) -> Vec<char>
    requires
        0 <= k,
        orig < pow2(k),
    ensures
        Str2Int(res@) == orig,
        ValidBitString(res@),
        res.len() == k as nat,
{
    let mut res = Vec::new();
    if k == 0 {
        return res;
    }
    let mut pow: nat = 1;
    let mut idx: int = 1;
    while idx < k
        invariant
            1 <= pow,
            1 <= idx && idx <= k,
        decreases k - idx
    {
        pow = pow * 2;
        idx += 1;
    }
    let mut cur: nat = orig;
    let mut i: int = 0;
    while i < k
        invariant
            0 <= i && i <= k,
        decreases k - i
    {
        let bit = if cur >= pow { '1' } else { '0' };
        if cur >= pow {
            cur = cur - pow;
        }
        res.push(bit);
        pow = pow / 2;
        i += 1;
    }
    res
}

// </vc-helpers>

// <vc-spec>
exec fn DivMod_Compare_Sub(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
{
    let n = dividend.len() as int;
    let d = Str2Int(divisor@);
    let mut q: Vec<char> = Vec::new();
    let mut rem: nat = 0;
    let mut i: int = 0;
    while i < n
        invariant
            0 <= i && i <= n,
            ValidBitString(q@),
        decreases n - i
    {
        let b = if dividend[i] == '1' { 1 } else { 0 };
        rem = rem * 2 + (b as nat);
        if rem >= d {
            q.push('1');
            rem = rem - d;
        } else {
            q.push('0');
        }
        i += 1;
    }
    let r = rem_to_bits(rem, divisor.len() as int);
    (q, r)
}

// </vc-code>

fn main() {}
}

