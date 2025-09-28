// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed types to use int instead of usize for Verus compatibility */
fn lemma_string_endswith_correctness(s: &str, suffix: &str)
    ensures string_ends_with(s@, suffix@) == (
        if suffix.len() > s.len() {
            false
        } else {
            s@.subrange(s.len() - suffix.len(), s.len() as int) == suffix@
        }
    )
{
}

fn lemma_char_comparison(s1: &str, s2: &str, start: int, len: int)
    requires 
        start >= 0,
        len >= 0,
        start + len <= s1.len(),
        len == s2.len()
    ensures
        (forall|k: int| 0 <= k < len ==> s1@[start + k] == s2@[k]) <==> 
        s1@.subrange(start, start + len) == s2@
{
}
// </vc-helpers>

// <vc-spec>
spec fn string_ends_with(s: Seq<char>, suffix: Seq<char>) -> bool {
    if suffix.len() > s.len() {
        false
    } else {
        s.subrange(s.len() - suffix.len(), s.len() as int) == suffix
    }
}

fn endswith(a: Vec<String>, suffix: Vec<String>) -> (result: Vec<bool>)
    requires a.len() == suffix.len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> {
            /* Main specification: result matches string_ends_with for each pair */
            result[i] == string_ends_with(a[i]@, suffix[i]@) &&
            /* Mathematical property: if result is true, suffix appears at the end */
            (result[i] ==> {
                suffix[i]@.len() <= a[i]@.len() &&
                a[i]@.subrange(a[i]@.len() - suffix[i]@.len(), a[i]@.len() as int) == suffix[i]@
            }) &&
            /* Mathematical property: if result is false, suffix does not appear at the end */
            (!result[i] ==> {
                suffix[i]@.len() > a[i]@.len() ||
                a[i]@.subrange(a[i]@.len() - suffix[i]@.len(), a[i]@.len() as int) != suffix[i]@
            })
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed index types to int for Verus sequence indexing */
    let mut result = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                result[j] == string_ends_with(a[j]@, suffix[j]@)
            }
    {
        let s = &a[i];
        let suf = &suffix[i];
        
        let ends_with = if suf.len() > s.len() {
            false
        } else {
            let start_pos = (s.len() - suf.len()) as int;
            let mut matches = true;
            let mut k = 0;
            while k < suf.len() && matches
                invariant
                    0 <= k <= suf.len(),
                    matches == (forall|idx: int| 0 <= idx < k ==> s@.index(start_pos + idx) == suf@.index(idx as int))
            {
                if s@.index(start_pos + (k as int)) != suf@.index(k as int) {
                    matches = false;
                }
                k += 1;
            }
            matches
        };
        
        proof {
            lemma_string_endswith_correctness(s, suf);
            if suf.len() <= s.len() {
                lemma_char_comparison(s, suf, (s.len() - suf.len()) as int, suf.len() as int);
            }
        }
        
        result.push(ends_with);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}