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
/* helper modified by LLM (iteration 4): Removed incorrect syntax in ensures clause. */
proof fn lemma_validate_not_empty(s: Seq<char>) ensures (Str2Int(s) > 0) == (s.len() > 0) {}
// </vc-helpers>

// <vc-spec>
exec fn NormalizeBitString(s: &[char]) -> (t: Vec<char>)
  ensures ValidBitString(t@), t@.len() > 0, (t@.len() > 1 ==> t@[0] != '0'), ValidBitString(s@) ==> Str2Int(s@) == Str2Int(t@)
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    while i < s.len()
        invariant 0 <= i && i <= s.len()
        decreases s.len() - i
    {
        if s[i] == '1' {
            break;
        }
        i = i + 1;
    }

    let mut t_vec: Vec<char> = Vec::new();

    if i == s.len() {
        t_vec.push('0');
    } else {
        let mut j: usize = i;
        while j < s.len()
            invariant i <= j && j <= s.len()
            decreases s.len() - j
        {
            t_vec.push(s[j]);
            j = j + 1;
        }
    }
    t_vec
}
// </vc-code>

fn main() {}
}


