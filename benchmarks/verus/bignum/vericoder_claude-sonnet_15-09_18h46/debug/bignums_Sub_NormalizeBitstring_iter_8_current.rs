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
spec fn is_normalized(s: Seq<char>) -> bool {
    s.len() == 0 || s.index(s.len() as int - 1) == '1'
}

/* helper modified by LLM (iteration 8): fixed bounds checking in proof */
proof fn preserve_valid_bitstring_lemma(s: &[char], end: int)
    requires
        ValidBitString(s@),
        0 <= end <= s@.len(),
    ensures
        ValidBitString(s@.subrange(0, end)),
{
    let sub = s@.subrange(0, end);
    assert forall |i: int| 0 <= i && i < sub.len() implies (sub.index(i) == '0' || sub.index(i) == '1') by {
        if 0 <= i && i < sub.len() {
            assert(i < end);
            assert(i < s@.len());
            assert(sub.index(i) == s@.index(i));
        }
    }
}
// </vc-helpers>

// <vc-spec>
exec fn Bignums_Sub_NormalizeBitstring(s: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 8): fixed invariant by adding proper bounds and preserving validity */
    let mut result = Vec::new();
    
    // Find the first '1' from the right
    let mut first_one_pos = s.len();
    let mut i = s.len();
    while i > 0
        invariant
            i <= s.len(),
            first_one_pos <= s.len(),
            first_one_pos < s.len() ==> s@.index(first_one_pos as int) == '1',
            forall |j: int| first_one_pos < j && j < s.len() ==> s@.index(j) == '0',
            forall |j: int| i <= j && j < first_one_pos ==> s@.index(j) == '0',
        decreases i
    {
        i = i - 1;
        if s[i] == '1' {
            first_one_pos = i;
        }
    }
    
    if first_one_pos == s.len() {
        // No '1' found, return "0"
        result.push('0');
        proof {
            assert(result@.len() == 1);
            assert(result@.index(0) == '0');
            assert forall |k: int| 0 <= k && k < result@.len() implies (result@.index(k) == '0' || result@.index(k) == '1') by {
                if 0 <= k && k < result@.len() {
                    assert(k == 0);
                    assert(result@.index(k) == '0');
                }
            }
        }
    } else {
        // Copy from start to first_one_pos (inclusive)
        let mut j = 0;
        while j <= first_one_pos
            invariant
                j <= first_one_pos + 1,
                first_one_pos < s.len(),
                ValidBitString(result@),
                result@.len() == j,
                forall |k: int| 0 <= k && k < j ==> result@.index(k) == s@.index(k),
            decreases first_one_pos + 1 - j
        {
            result.push(s[j]);
            proof {
                assert(s@.index(j as int) == '0' || s@.index(j as int) == '1');
                let old_len = result@.len() - 1;
                assert(result@.index(old_len) == s@.index(j as int));
            }
            j = j + 1;
        }
    }
    
    result
}
// </vc-code>

fn main() {}
}
