// <vc-preamble>
use vstd::prelude::*;
use vstd::string::*;

verus! {
spec fn string_starts_with(s: Seq<char>, prefix: Seq<char>) -> bool {
    prefix.len() <= s.len() && s.subrange(0, prefix.len() as int) == prefix
}
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): Fixed type error by converting prefix@.len() to usize */
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
            },
    {
        let s = &a[i];
        let prefix = &prefixes[i];
        
        if prefix@.len() > s@.len() {
            result.push(false);
        } else {
            let mut matches = true;
            let mut j: usize = 0;
            let prefix_len = prefix@.len() as usize;
            
            while j < prefix_len
                invariant
                    0 <= j <= prefix_len,
                    prefix_len == prefix@.len(),
                    prefix@.len() <= s@.len(),
                    matches == (s@.subrange(0, j as int) == prefix@.subrange(0, j as int)),
            {
                if s.get_char(j) != prefix.get_char(j) {
                    matches = false;
                }
                j = j + 1;
            }
            
            assert(matches == (s@.subrange(0, prefix@.len() as int) == prefix@));
            assert(matches == string_starts_with(s@, prefix@));
            result.push(matches);
        }
        
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}