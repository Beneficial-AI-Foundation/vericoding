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
spec fn is_bit(c: char) -> bool { c == '0' || c == '1' }
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2_Mul(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
    let mut res = Vec::<char>::new();
    let mut i: int = 0;
    while i < b.len() as int
        invariant
            0 <= i,
            ValidBitString(res@),
        decreases b.len() as int - i
    {
        res.push(b[i as usize]);
        i = i + 1;
    }
    let mut j: int = 0;
    while j < a.len() as int
        invariant
            0 <= j,
            ValidBitString(res@),
        decreases a.len() as int - j
    {
        res.push(a[j as usize]);
        j = j + 1;
    }
    res
}
// </vc-code>

fn main() {}
}

