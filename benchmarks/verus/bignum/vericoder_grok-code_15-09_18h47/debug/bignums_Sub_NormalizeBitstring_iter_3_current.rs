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
    /* code modified by LLM (iteration 3): added decreases clauses to while loops to fix verification errors and prevent infinite loops */
    let s_len = s.len();
    let mut i: usize = 0;
    while i < s_len && s[i] == '0'
        invariant
            0 <= i as int <= s_len as int,
            forall |j: int| 0 <= j < i as int ==> s@.index(j) == '0',
        decreases (s_len - i) as int
    {
        i = i + 1;
    }
    if i == s_len {
        let mut res = Vec::<char>::new();
        res.push('0');
        return res;
    } else {
        let mut res = Vec::<char>::new();
        let mut j = i;
        while j < s_len
            invariant
                i as int <= j as int <= s_len as int,
            decreases (s_len - j) as int
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
