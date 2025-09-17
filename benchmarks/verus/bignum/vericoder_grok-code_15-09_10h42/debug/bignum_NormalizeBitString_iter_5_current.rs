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
/* helper modified by LLM (iteration 5): none */
// </vc-helpers>

// <vc-spec>
exec fn NormalizeBitString(s: &[char]) -> (t: Vec<char>)
  ensures ValidBitString(t@), t@.len() > 0, (t@.len() > 1 ==> t@[0] != '0'), ValidBitString(s@) ==> Str2Int(s@) == Str2Int(t@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fix compilation error by replacing for-in loop with index-based while loop */
    let mut collected = Vec::<char>::new();
    let mut i = 0;
    while i < s.len()
        invariant
            i <= s.len()
    {
        let c = s[i];
        if c == '0' || c == '1' {
            collected.push(c);
        }
        i += 1;
    }
    let mut t = Vec::<char>::new();
    if collected.len() == 0 {
        t.push('0');
    } else {
        let mut start = 0;
        while start < collected.len() && collected[start] == '0' {
            start += 1;
        }
        if start == collected.len() {
            t.push('0');
        } else {
            let mut j = start;
            while j < collected.len()
                invariant
                    start <= j <= collected.len()
            {
                t.push(collected[j]);
                j += 1;
            }
        }
    }
    t
}
// </vc-code>

fn main() {}
}


