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
    /* code modified by LLM (iteration 6): fixed type mismatches in invariants and decreases by using (i as int) and (j as int), and ensured postcondition */
    let s_len = s.len();
    let mut res: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < s_len && s[i] == '0'
        invariant
            0 <= i as int <= s@.len(),
            forall |k: int| 0 <= k < i as int ==> s@.index(k) == '0',
        decreases s@.len() - (i as int)
    {
        i += 1;
    }
    if i == s_len {
        res.push('0');
        return res;
    } else {
        let mut j: usize = i;
        while j < s_len
            invariant
                i as int <= j as int <= s@.len(),
            decreases s@.len() - (j as int)
        {
            res.push(s[j]);
            j += 1;
        }
        return res;
    }
}
// </vc-code>

fn main() {}
}
