// <vc-preamble>
use vstd::prelude::*;
use vstd::string::*;

verus! {
spec fn string_starts_with(s: Seq<char>, prefix: Seq<char>) -> bool {
    prefix.len() <= s.len() && s.subrange(0, prefix.len() as int) == prefix
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed len compilation error by using sequence view @ for Strings */
fn exec_string_starts_with(a: &String, b: &String) -> (result: bool)
    ensures
        result == string_starts_with(a@, b@),
{
    if b@.len() > a@.len() {
        false
    } else {
        let mut j: usize = 0;
        let mut matches: bool = true;
        while j < b@.len() as usize && matches
            invariant
                matches ==> (forall|k: int| 0 <= k < j as int ==> a@[k] == b@[k]),
                (forall|k: int| 0 <= k < j as int ==> a@[k] == b@[k]) ==> matches,
                0 <= j as int <= (b@.len() as int),
            decreases (b@.len() as int) - (j as int)
        {
            let a_char = a.as_bytes()[j] as char;
            let b_char = b.as_bytes()[j] as char;
            if a_char != b_char {
                matches = false;
            }
            j += 1;
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
/* code modified by LLM (iteration 5): unchanged, compilation error fixed in helper */
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            result.len() == i as int,
            forall|j: int| 0 <= j < i ==> result@[j] == string_starts_with(a@[j]@, prefixes@[j]@),
        decreases a.len() - i
    {
        let starts = exec_string_starts_with(&a[i], &prefixes[i]);
        result.push(starts);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}