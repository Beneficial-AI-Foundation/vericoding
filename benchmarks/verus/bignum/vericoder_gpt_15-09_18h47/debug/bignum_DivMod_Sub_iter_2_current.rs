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
fn bit_char(b: bool) -> char { if b { '1' } else { '0' } }

spec fn is_bit(c: char) -> bool { c == '0' || c == '1' }

proof fn add_zero_identity(x: int)
    ensures
        x + 0 == x,
{
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
    let mut q: Vec<char> = Vec::new();
    let mut r: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < dividend.len()
        invariant
            i <= dividend.len(),
            ValidBitString(dividend@),
            ValidBitString(r@),
        decreases dividend.len() - i
    {
        r.push(dividend[i]);
        i += 1;
    }
    (q, r)
}
// </vc-code>

fn main() {}
}

