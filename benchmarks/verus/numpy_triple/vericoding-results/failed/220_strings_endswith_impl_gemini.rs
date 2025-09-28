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
    /* code modified by LLM (iteration 5): used StrSlice API to access string length and substrings with specifications */
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            a.len() == suffix.len(),
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < (i as int) ==> result@[j] == string_ends_with(a@[j]@, suffix@[j]@),
        decreases a.len() - i
    {
        let s = &a[i];
        let suff = &suffix[i];

        let s_slice = s.as_str_slice();
        let suff_slice = suff.as_str_slice();

        let ends = if suff_slice.len() > s_slice.len() {
            false
        } else {
            let start_index = (s_slice.len() - suff_slice.len()) as usize;
            let end_index = s_slice.len() as usize;
            let s_suffix_str = s_slice.substring_char(start_index, end_index);
            s_suffix_str == *suff
        };

        result.push(ends);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}