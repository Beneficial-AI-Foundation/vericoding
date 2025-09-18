// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed mismatched types error by using explicit `String::substring_ascii` call. */
fn partition_string(s: String, sep: String) -> (result: (String, String, String))
    ensures
        result.0@ + result.1@ + result.2@ == s@,
        (result.1@ == sep@ || result.1.len() == 0),
        (result.1.len() == 0 ==> result.2.len() == 0 && result.0@ == s@),
        s.len() == result.0.len() + result.1.len() + result.2.len(),
{
    if sep.len() == 0 {
        return (s.clone(), String::new(), String::new());
    }
    match s.find(sep.as_str()) {
        Some(idx) => {
            let before = String::substring_ascii(&s, 0, idx);
            let sep_found = String::substring_ascii(&s, idx, idx + sep.len());
            let after = String::substring_ascii(&s, idx + sep.len(), s.len());
            (before, sep_found, after)
        }
        None => {
            (s.clone(), String::new(), String::new())
        }
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
{
    /* code modified by LLM (iteration 5): No changes needed as the fix was in the helper function. */
    let mut befores: Vec<String> = Vec::new();
    let mut seps: Vec<String> = Vec::new();
    let mut afters: Vec<String> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            befores.len() == i,
            seps.len() == i,
            afters.len() == i,
            forall|j: int| 0 <= j < i as int ==> {
                let original = #[trigger] a[j]@;
                let before_j = befores[j]@;
                let sep_j = seps[j]@;
                let after_j = afters[j]@;
                &&& before_j + sep_j + after_j == original
                &&& (sep_j == sep@ || sep_j.len() == 0)
                &&& (sep_j.len() == 0 ==> after_j.len() == 0 && before_j == original)
                &&& original.len() == before_j.len() + sep_j.len() + after_j.len()
            }
    {
        let (before, sep_part, after) = partition_string(a[i].clone(), sep.clone());
        befores.push(before);
        seps.push(sep_part);
        afters.push(after);
        i = i + 1;
    }
    (befores, seps, afters)
}
// </vc-code>

}
fn main() {}