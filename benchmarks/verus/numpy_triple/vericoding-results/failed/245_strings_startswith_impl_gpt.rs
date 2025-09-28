// <vc-preamble>
use vstd::prelude::*;
use vstd::string::*;

verus! {
spec fn string_starts_with(s: Seq<char>, prefix: Seq<char>) -> bool {
    prefix.len() <= s.len() && s.subrange(0, prefix.len() as int) == prefix
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): definitional equivalence for string_starts_with */
proof fn lemma_string_starts_with_def_equiv(s: String, p: String)
    ensures
        string_starts_with(s@, p@) == (p@.len() <= s@.len() && s@.subrange(0, p@.len() as int) == p@),
{
}

/* helper modified by LLM (iteration 5): relate String::len() to view length */
proof fn lemma_string_len_view_len(s: String)
    ensures
        s.len() as int == s@.len(),
{
    let l = s.len();
    assert(l as int == s@.len());
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
{
    /* code modified by LLM (iteration 5): use String::starts_with instead of nonexistent slice_range; maintain invariant via method's spec */
    let n = a.len();
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            result.len() == i,
            i <= n,
            n == a.len(),
            n == prefixes.len(),
            forall|k: int| 0 <= k < i as int ==> result[k] == string_starts_with(a[k]@, prefixes[k]@),
        decreases n - i
    {
        let ai = a[i].clone();
        let pi = prefixes[i].clone();
        let cond = ai.starts_with(&pi);
        result.push(cond);
        proof {
            let ii: int = i as int;
            assert(0 <= ii && ii < a.len() as int);
            assert(0 <= ii && ii < prefixes.len() as int);
            // After push, new element is at index ii
            assert(result[ii] == cond);
            // Connect cloned values back to originals at index ii
            assert(a[ii] == ai);
            assert(prefixes[ii] == pi);
            // By the spec of String::starts_with from vstd::string, cond matches our string_starts_with predicate on views
            assert(cond == string_starts_with(ai@, pi@));
            assert(a[ii]@ == ai@);
            assert(prefixes[ii]@ == pi@);
            assert(result[ii] == string_starts_with(a[ii]@, prefixes[ii]@));
        }
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}