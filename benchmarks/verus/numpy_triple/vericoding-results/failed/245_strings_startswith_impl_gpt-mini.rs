// <vc-preamble>
use vstd::prelude::*;
use vstd::string::*;

verus! {
spec fn string_starts_with(s: Seq<char>, prefix: Seq<char>) -> bool {
    prefix.len() <= s.len() && s.subrange(0, prefix.len() as int) == prefix
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): equivalence between String and spec predicate */
proof fn lemma_string_starts_with_equiv(s: String, prefix: String)
    ensures
        (prefix@.len() <= s@.len() && s@.subrange(0, prefix@.len() as int) == prefix@) == string_starts_with(s@, prefix@),
{
    proof {
        assert(string_starts_with(s@, prefix@) == (prefix@.len() <= s@.len() && s@.subrange(0, prefix@.len() as int) == prefix@));
    }
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
    /* code modified by LLM (iteration 5): iterate vectors using usize indexing and maintain spec invariant */
    let mut res: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    let n: usize = a.len();
    while i < n
        invariant
            res.len() == i,
            forall|j: int| 0 <= j < i as int ==> res[j] == string_starts_with(a[j]@, prefixes[j]@),
        decreases n as int - i as int
    {
        let b: bool = string_starts_with(a[i as int]@, prefixes[i as int]@);
        res.push(b);
        proof {
            assert(res[i as int] == string_starts_with(a[i as int]@, prefixes[i as int]@));
        }
        i = i + 1;
    }
    res
}
// </vc-code>


}
fn main() {}