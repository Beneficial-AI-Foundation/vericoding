// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No changes were required for this helper after fixing the compilation errors in the main code block. */
spec fn contains_sep(s: &str, sep: &str) -> bool {
    s.contains(sep)
}

spec fn find_first_sep(s: &str, sep: &str) -> int
    decreases s.len()
{
    if s.len() < sep.len() || !contains_sep(s, sep) {
        s.len() as int
    } else if s.subslice(0, sep.len() as int) == sep {
        0
    } else {
        1 + find_first_sep(s.subslice(1, s.len() as int), sep)
    }
}
// </vc-helpers>

// <vc-spec>
fn partition(a: Vec<String>, sep: String) -> (result: (Vec<String>, Vec<String>, Vec<String>))
    ensures
        result.0.len() == a.len() && result.1.len() == a.len() && result.2.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> {
            let original = #[trigger] a[i]@;
            let before_i = result.0[i]@;
            let sep_i = result.1[i]@;
            let after_i = result.2[i]@;

            before_i + sep_i + after_i == original &&

            (sep_i == sep@ || sep_i.len() == 0) &&

            (sep_i.len() == 0 ==> after_i.len() == 0 && before_i == original) &&

            original.len() == before_i.len() + sep_i.len() + after_i.len()
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Changed `sep.len() as int` to `sep.len() as usize` and `element.len() as int` to `element.len()as usize` within `element.subslice` calls for fixing compilation errors. */
{
    let mut before: Vec<String> = Vec::new();
    let mut sep_parts: Vec<String> = Vec::new();
    let mut after: Vec<String> = Vec::new();

    let mut i = 0;
    while i < a.len()
        invariant
             0 <= i <= a.len(),
             before.len() == i,
             sep_parts.len() == i,
             after.len() == i,
             forall|j: int| 0 <= j < i ==> {
                let original = #[trigger] a[j]@;
                let b_j = before[j]@;
                let s_j = sep_parts[j]@;
                let a_j = after[j]@;

                 b_j + s_j + a_j == original &&

                 (s_j == sep@ || s_j.len() == 0) &&

                 (s_j.len() == 0 ==> a_j.len() == 0 && b_j == original) &&

                 original.len() == b_j.len() + s_j.len() + a_j.len()
            }
    {
        let element = &a[i]; // Use a reference to the element to avoid ownership issues
        if contains_sep(element.view(), sep.view()) {
            let sep_idx = find_first_sep(element.view(), sep.view());
            let b = String::from_str(element.subslice(0, sep_idx as usize));
            let s = sep.clone();
            let af = String::from_str(element.subslice((sep_idx + sep.len() as int) as usize, element.len() as usize));
            before.push(b);
            sep_parts.push(s);
            after.push(af);
        } else {
            before.push(element.clone());
            sep_parts.push(String::new());
            after.push(String::new());
        }
        i = i + 1;
    }
    (before, sep_parts, after)
}
// </vc-code>

}
fn main() {}