// <vc-preamble>
use vstd::prelude::*;
use vstd::string::*;

verus! {
spec fn string_starts_with(s: Seq<char>, prefix: Seq<char>) -> bool {
    prefix.len() <= s.len() && s.subrange(0, prefix.len() as int) == prefix
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Replace internal helper with spec-compatible version to address verification error. */
spec fn string_starts_with_internal_spec(s: Seq<char>, prefix: Seq<char>) -> bool {
    prefix.len() <= s.len() && s.subrange(0, prefix.len() as int) == prefix
}
// </vc-helpers>

// <vc-spec>
fn startswith(a: Vec<String>, prefixes: Vec<String>) -> (result: Vec<bool>)
    requires a.len() == prefixes.len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> {
            &&& (result[i] == string_starts_with(a[i]@, prefixes[i]@))
            &&& (result[i] ==> prefixes[i]@.len() <= a[i]@.len())
            &&& (result[i] ==> a[i]@.subrange(0, prefixes[i]@.len() as int) == prefixes[i]@)
            &&& (!result[i] ==> (prefixes[i]@.len() > a[i]@.len() || a[i]@.subrange(0, prefixes[i]@.len() as int) != prefixes[i]@))
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected type casting from `nat` to `usize` for `Seq` indexing. */
{
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;

    while i < a.len()
        invariant
            0 <= i && i <= a.len(),
            result.len() == i,
            a.len() == prefixes.len(),
            forall|j: int| 0 <= j < i ==> {
                &&& (result[j] == string_starts_with_internal_spec(a[j as usize]@, prefixes[j as usize]@))
                &&& (result[j] ==> prefixes[j as usize]@.len() <= a[j as usize]@.len())
                &&& (result[j] ==> a[j as usize]@.subrange(0, prefixes[j as usize]@.len() as int) == prefixes[j as usize]@)
                &&& (!result[j] ==> (prefixes[j as usize]@.len() > a[j as usize]@.len() || a[j as usize]@.subrange(0, prefixes[j as usize]@.len() as int) != prefixes[j as usize]@))
            }
        decreases a.len() - i
    {
        let s = a[i].view();
        let prefix = prefixes[i].view();
        let mut starts: bool = false;

        if prefix.len() <= s.len() {
            let mut j: usize = 0;
            starts = true;
            while j < prefix.len()
                invariant
                    0 <= j && j <= prefix.len(),
                    j <= s.len(), // Follows from prefix.len() <= s.len()
                    starts == (forall|k: int| 0 <= k < j ==> s[k as usize] == prefix[k as usize]),
                    prefix.len() <= s.len(),
                    s.len() >= 0,
                    prefix.len() >= 0,
                decreases prefix.len() - j
            {
                if s[j as usize] != prefix[j as usize] {
                    starts = false;
                }
                j = j + 1;
            }
        }
        result.push(starts);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}