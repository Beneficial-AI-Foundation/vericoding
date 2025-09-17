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

// </vc-helpers>

// <vc-spec>
exec fn Bignums_Sub_NormalizeBitstring(s: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added decreases clauses to loops */
    let mut res: Vec<char> = Vec::new();
    let mut i = 0;
    while i < s.len()
        invariant
            i <= s@.len(),
        decreases s@.len() - i
    {
        if s[i] == '1' {
            break;
        }
        i += 1;
    }
    if i == s.len() {
        res.push('0');
    } else {
        while i < s.len()
            invariant
                i <= s@.len(),
            decreases s@.len() - i
        {
            res.push(s[i]);
            i += 1;
        }
    }
    res
}
// </vc-code>

fn main() {}
}
