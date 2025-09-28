// <vc-preamble>
use vstd::prelude::*;
use vstd::string::*;

verus! {
spec fn string_starts_with(s: Seq<char>, prefix: Seq<char>) -> bool {
    prefix.len() <= s.len() && s.subrange(0, prefix.len() as int) == prefix
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed compilation error by using unicode_len for exec string lengths and spec length for specs */
fn exec_string_starts_with(s: &String, prefix: &String) -> (result: bool)
    ensures result == string_starts_with(s@, prefix@),
{
    if prefix.unicode_len() > s.unicode_len() {
        return false;
    }

    let mut i: usize = 0;
    while i < prefix.unicode_len()
        invariant
            prefix@.len() <= s@.len(),
            i <= prefix@.len(),
            s@.subrange(0, i as int) == prefix@.subrange(0, i as int),
        decreases prefix@.len() - i
    {
        if s.get_char(i) != prefix.get_char(i) {
            return false;
        }
        i = i + 1;
    }
    
    true
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
/* code modified by LLM (iteration 5): no changes needed as the fix was in the helper function */
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            a.len() == prefixes.len(),
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> result@[j] == string_starts_with(a@[j]@, prefixes@[j]@),
        decreases a.len() - i
    {
        let b = exec_string_starts_with(&a[i], &prefixes[i]);
        result.push(b);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}