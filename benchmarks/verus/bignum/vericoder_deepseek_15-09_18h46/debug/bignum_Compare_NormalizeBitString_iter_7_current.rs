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
  // All characters must be '0' or '1'.
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
/* helper modified by LLM (iteration 7): Fixed lemma syntax - removed 'proof' keyword */
lemma_int_cast(n: u64)
    ensures n as int == (n as int)
{
}

/* helper modified by LLM (iteration 7): Fixed lemma syntax - removed 'proof' keyword */
lemma_str2int_monotonic(s: Seq<char>, t: Seq<char>)
    requires
        ValidBitString(s),
        ValidBitString(t),
        s.len() <= t.len(),
    ensures
        Str2Int(s) <= Str2Int(t),
    decreases s.len()
{
    if s.len() == 0 {
        assert(Str2Int(s) == 0) by (compute);
    } else {
        let s_prefix = s.subrange(0, s.len() as int - 1);
        let t_prefix = t.subrange(0, t.len() as int - 1);
        lemma_str2int_monotonic(s_prefix, t_prefix);
    }
}

/* helper modified by LLM (iteration 7): Fixed lemma syntax - removed 'proof' keyword */
lemma_str2int_prefix(s: Seq<char>, i: int)
    requires
        ValidBitString(s),
        0 <= i && i <= s.len() as int,
    ensures
        Str2Int(s.subrange(0, i)) <= Str2Int(s),
    decreases i
{
    if i < s.len() as int {
        lemma_str2int_prefix(s, i + 1);
    }
}
// </vc-helpers>

// <vc-spec>
exec fn Compare(s1: &[char], s2: &[char]) -> (res: i32)
  requires ValidBitString(s1@),
   ValidBitString(s2@),
  ensures Str2Int(s1@) < Str2Int(s2@) ==> res == -1,
    Str2Int(s1@) == Str2Int(s2@) ==> res == 0,
    Str2Int(s1@) > Str2Int(s2@) ==> res == 1,
  decreases Str2Int(s1@) + Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 7): Removed nested proof function and fixed ghost block implementation */
{
    let len1 = s1.len();
    let len2 = s2.len();
    ghost {
        let len1_int: int = len1 as int;
        let len2_int: int = len2 as int;
        let mut i: int = 0;
        let min_len = if len1_int < len2_int { len1_int } else { len2_int };

        while i < min_len
            invariant
                0 <= i && i <= min_len,
                forall |j: int| 0 <= j && j < i ==> s1@[j] == s2@[j],
                Str2Int(s1@.subrange(0, i)) == Str2Int(s2@.subrange(0, i)),
            decreases min_len - i
        {
            if s1@[i] != s2@[i] {
                if s1@[i] == '0' {
                    proof {
                        lemma_str2int_monotonic(s1@.subrange(i + 1, len1_int), s2@.subrange(i + 1, len2_int));
                    }
                    return -1;
                } else {
                    proof {
                        lemma_str2int_monotonic(s2@.subrange(i + 1, len2_int), s1@.subrange(i + 1, len1_int));
                    }
                    return 1;
                }
            }
            i += 1;
        }

        if len1_int < len2_int {
            proof {
                lemma_str2int_monotonic(s1@, s2@);
            }
            return -1;
        } else if len1_int > len2_int {
            proof {
                lemma_str2int_monotonic(s2@, s1@);
            }
            return 1;
        } else {
            return 0;
        }
    }
}
// </vc-code>

fn main() {}
}


