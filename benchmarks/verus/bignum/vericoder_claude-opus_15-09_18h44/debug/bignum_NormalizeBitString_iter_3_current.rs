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
proof fn lemma_str2int_zero(s: Seq<char>)
    requires
        ValidBitString(s),
        forall |i: int| 0 <= i && i < s.len() ==> s[i] == '0',
    ensures
        Str2Int(s) == 0,
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        lemma_str2int_zero(s.subrange(0, s.len() - 1));
    }
}

proof fn lemma_str2int_append(s: Seq<char>, c: char)
    requires
        ValidBitString(s),
        c == '0' || c == '1',
    ensures
        Str2Int(s.push(c)) == 2 * Str2Int(s) + if c == '1' { 1nat } else { 0nat },
{
    let s_new = s.push(c);
    assert(s_new.subrange(0, s_new.len() - 1) =~= s);
}

/* helper modified by LLM (iteration 3): added lemma for subrange equality */
proof fn lemma_str2int_subrange(s: Seq<char>, start: int, end: int)
    requires
        ValidBitString(s),
        0 <= start <= end <= s.len(),
        ValidBitString(s.subrange(start, end)),
    ensures
        Str2Int(s.subrange(start, end)) == Str2Int(s.subrange(start, end)),
// </vc-helpers>

// <vc-spec>
exec fn NormalizeBitString(s: &[char]) -> (t: Vec<char>)
  ensures ValidBitString(t@), t@.len() > 0, (t@.len() > 1 ==> t@[0] != '0'), ValidBitString(s@) ==> Str2Int(s@) == Str2Int(t@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): simplified logic to properly track normalization */
    let mut result = Vec::<char>::new();
    let mut start_idx: usize = 0;
    let mut found_start = false;
    
    // Find the first non-zero character
    for i in 0..s.len()
        invariant
            0 <= i <= s.len(),
            !found_start ==> forall |j: int| 0 <= j && j < i ==> ValidBitString(s@) ==> s@[j] == '0',
            found_start ==> start_idx < i && ValidBitString(s@) ==> s@[start_idx as int] != '0',
    {
        if s[i] != '0' && !found_start {
            start_idx = i;
            found_start = true;
        }
    }
    
    // Copy from start_idx to end
    if found_start {
        for i in start_idx..s.len()
            invariant
                start_idx <= i <= s.len(),
                ValidBitString(result@),
                result@.len() == i - start_idx,
                ValidBitString(s@) ==> (
                    forall |j: int| 0 <= j && j < result@.len() ==>
                        result@[j] == s@[start_idx as int + j]
                ),
                ValidBitString(s@) && result@.len() > 0 ==> result@[0] != '0',
                ValidBitString(s@) ==> Str2Int(result@) == Str2Int(s@.subrange(start_idx as int, i as int)),
        {
            result.push(s[i]);
            proof {
                if ValidBitString(s@) {
                    lemma_str2int_append(result@.subrange(0, result@.len() - 1), s@[i as int]);
                    assert(result@[result@.len() - 1] == s@[i as int]);
                }
            }
        }
        proof {
            if ValidBitString(s@) {
                lemma_str2int_zero(s@.subrange(0, start_idx as int));
                lemma_str2int_subrange(s@, start_idx as int, s.len() as int);
            }
        }
    } else {
        // All zeros or empty
        result.push('0');
        proof {
            if ValidBitString(s@) {
                lemma_str2int_zero(s@);
            }
        }
    }
    
    result
}
// </vc-code>

fn main() {}
}


