// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): add missing helper */
spec fn string_ends_with_vec(s: &StrSlice, suffix: &StrSlice) -> bool {
    if suffix.len() > s.len() {
        false
    } else {
        s.get_view().subrange(s.len() - suffix.len(), s.len() as int) == suffix.get_view()
    }
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
/* code modified by LLM (iteration 5): Correct string_ends_with usage and parameters, remove redundant checks */
{
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;

    while i < a.len()
        invariant
            0 <= i as int && i as int <= a.len() as int,
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> {
                result[j as usize] == string_ends_with(a[j as usize]@, suffix[j as usize]@)
            }
    {
        let a_str = &a[i];
        let suffix_str = &suffix[i];

        let ends_with = string_ends_with_vec(a_str, suffix_str);
        
        result.push(ends_with);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}