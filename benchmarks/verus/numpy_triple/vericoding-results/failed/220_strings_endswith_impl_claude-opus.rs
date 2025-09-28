// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): fix nat/int type mismatches */
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            a.len() == suffix.len(),
            forall|j: int| 0 <= j < i ==> {
                result[j] == string_ends_with(a[j]@, suffix[j]@) &&
                (result[j] ==> {
                    suffix[j]@.len() <= a[j]@.len() &&
                    a[j]@.subrange(a[j]@.len() - suffix[j]@.len(), a[j]@.len() as int) == suffix[j]@
                }) &&
                (!result[j] ==> {
                    suffix[j]@.len() > a[j]@.len() ||
                    a[j]@.subrange(a[j]@.len() - suffix[j]@.len(), a[j]@.len() as int) != suffix[j]@
                })
            },
    {
        let a_str = &a[i];
        let suffix_str = &suffix[i];
        
        if suffix_str@.len() > a_str@.len() {
            result.push(false);
        } else {
            let start_idx: int = (a_str@.len() - suffix_str@.len()) as int;
            let mut matches = true;
            let mut j: int = 0;
            
            while j < suffix_str@.len()
                invariant
                    0 <= j <= suffix_str@.len(),
                    suffix_str@.len() <= a_str@.len(),
                    start_idx == (a_str@.len() - suffix_str@.len()) as int,
                    matches == (a_str@.subrange(start_idx, start_idx + j) == suffix_str@.subrange(0, j)),
                    forall|k: int| 0 <= k < j ==> a_str@.index(start_idx + k) == suffix_str@.index(k),
            {
                if a_str@.index(start_idx + j) != suffix_str@.index(j) {
                    matches = false;
                }
                j = j + 1;
            }
            
            assert(j == suffix_str@.len());
            if matches {
                assert(a_str@.subrange(start_idx, a_str@.len() as int) == suffix_str@);
            }
            result.push(matches);
        }
        
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}