// <vc-preamble>
use vstd::prelude::*;
use vstd::string::*;

verus! {
spec fn string_starts_with(s: Seq<char>, prefix: Seq<char>) -> bool {
    prefix.len() <= s.len() && s.subrange(0, prefix.len() as int) == prefix
}
// </vc-preamble>

// <vc-helpers>
fn check_startswith(s: &String, prefix: &String) -> (result: bool)
    ensures 
        result == string_starts_with(s@, prefix@),
        result ==> prefix@.len() <= s@.len(),
        result ==> s@.subrange(0, prefix@.len() as int) == prefix@,
        !result ==> (prefix@.len() > s@.len() || s@.subrange(0, prefix@.len() as int) != prefix@)
{
    if prefix.len() > s.len() {
        false
    } else {
        let prefix_chars = prefix.as_str().chars();
        let s_chars = s.as_str().chars();
        
        let mut i = 0;
        while i < prefix.len()
            invariant
                0 <= i <= prefix.len(),
                prefix.len() <= s.len(),
                forall|j: int| 0 <= j < i ==> s@[j] == prefix@[j]
        {
            if s_chars.nth(i) != prefix_chars.nth(i) {
                return false;
            }
            i += 1;
        }
        true
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
    /* code modified by LLM (iteration 5): kept implementation from previous iteration */
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            a.len() == prefixes.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                &&& (result[j] == string_starts_with(a[j]@, prefixes[j]@))
                &&& (result[j] ==> prefixes[j]@.len() <= a[j]@.len())
                &&& (result[j] ==> a[j]@.subrange(0, prefixes[j]@.len() as int) == prefixes[j]@)
                &&& (!result[j] ==> (prefixes[j]@.len() > a[j]@.len() || a[j]@.subrange(0, prefixes[j]@.len() as int) != prefixes[j]@))
            }
    {
        let starts = check_startswith(&a[i], &prefixes[i]);
        result.push(starts);
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}