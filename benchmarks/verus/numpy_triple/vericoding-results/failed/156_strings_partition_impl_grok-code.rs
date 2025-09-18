// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): corrected ensures to use subrange for subsequence comparisons instead of invalid range indexing */
fn find_sep_index(s: &str, sep: &str) -> (r: usize)
    ensures
        (r as int) <= ((s.len() as int) - (sep.len() as int) + 1),
        forall|j: int| 0 <= j < (r as int) ==> s@.subrange(j, j + (sep.len() as int)) != sep@,
        ((r as int) < ((s.len() as int) - (sep.len() as int) + 1)) ==> s@.subrange((r as int), (r as int) + (sep.len() as int)) == sep@,
        ((r as int) == ((s.len() as int) - (sep.len() as int) + 1)) ==> forall|j: int| 0 <= j <= ((s.len() as int) - (sep.len() as int)) ==> s@.subrange(j, j + (sep.len() as int)) != sep@
{
    let mut idx: usize = 0;
    while idx + sep.len() <= s.len()
    {
        if &s[idx..idx+sep.len()] == sep {
            return idx;
        }
        idx += 1;
    }
    return idx;
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
/* code modified by LLM (iteration 5): fixed compilation by using sep.len() for comparison instead of sep_seq.len() to match exec type */
{
    let sep_seq = sep@;
    let alen = a.len();
    let mut before_vec = Vec::new();
    let mut sep_vec = Vec::new();
    let mut after_vec = Vec::new();
    if sep.len() == 0 {
        let mut i = 0;
        while i < alen
            invariant before_vec@.len() == i,
                sep_vec@.len() == i,
                after_vec@.len() == i,
                0 <= i <= alen
        {
            before_vec.push(a[i].clone());
            sep_vec.push(String::new());
            after_vec.push(String::new());
            i += 1;
        }
    } else {
        let seplen = sep.len();
        let mut i = 0;
        while i < alen
            invariant before_vec@.len() == i,
                sep_vec@.len() == i,
                after_vec@.len() == i,
                0 <= i <= alen
        {
            let s = a[i].as_str();
            let idx = find_sep_index(s, sep.as_str());
            let slen = s.len();
            if idx < slen - seplen + 1 {
                before_vec.push(String::from(&s[0..idx]));
                sep_vec.push(sep.clone());
                after_vec.push(String::from(&s[idx + seplen..]));
            } else {
                before_vec.push(String::from(s));
                sep_vec.push(String::new());
                after_vec.push(String::new());
            }
            i += 1;
        }
    }
    return (before_vec, sep_vec, after_vec);
}
// </vc-code>

}
fn main() {}