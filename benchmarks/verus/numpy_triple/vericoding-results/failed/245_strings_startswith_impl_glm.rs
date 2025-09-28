// <vc-preamble>
use vstd::prelude::*;
use vstd::string::*;

verus! {
spec fn string_starts_with(s: Seq<char>, prefix: Seq<char>) -> bool {
    prefix.len() <= s.len() && s.subrange(0, prefix.len() as int) == prefix
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fixed type errors in loop condition and indexing */
exec fn string_starts_with_exec(s: &String, prefix: &String) -> (b: bool)
    ensures b == string_starts_with(s@, prefix@)
{
    if prefix@.len() > s@.len() {
        false
    } else {
        let mut i = 0;
        let mut matches = true;
        while i < prefix@.len() as int && matches
            invariant 
                0 <= i <= prefix@.len() as int,
                matches ==> forall|j: nat| j < i ==> s@[j] == prefix@[j],
                !matches ==> exists|j: nat| j < i+1 && s@[j] != prefix@[j],
            decreases (prefix@.len() as int) - i
        {
            if s@[i as nat] != prefix@[i as nat] {
                matches = false;
            } else {
                i += 1;
            }
        }
        matches
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
/* code modified by LLM (iteration 2): simplified implementation using direct sequence access */
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant 
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == string_starts_with(a[j]@, prefixes[j]@),
        decreases a.len() - i
    {
        let flag = string_starts_with_exec(&a[i], &prefixes[i]);
        result.push(flag);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}