// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed ensures clause syntax using let-in */
fn split_at_separator(s: String, sep: String) -> (String, String, String)
    ensures
        let (before, sep_part, after) = split_at_separator(s, sep) in
            s@ == before@ + sep_part@ + after@ &&
            (sep_part@ == sep@ || sep_part@ == "") &&
            (sep_part@ == "" ==> after@ == "" && before@ == s@)
{
    let sep_len = sep.len();
    if sep_len == 0 {
        (s, String::new(), String::new())
    } else {
        if let Some(pos) = s.find(sep.as_str()) {
            let before = s[0..pos].to_string();
            let sep_part = s[pos..pos+sep_len].to_string();
            let after = s[pos+sep_len..].to_string();
            (before, sep_part, after)
        } else {
            (s, String::new(), String::new())
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
/* code modified by LLM (iteration 5): no changes needed */
{
    let mut before_vec = Vec::new();
    let mut sep_vec = Vec::new();
    let mut after_vec = Vec::new();

    for s in a {
        let (before, sep_part, after) = split_at_separator(s, sep);
        before_vec.push(before);
        sep_vec.push(sep_part);
        after_vec.push(after);
    }

    (before_vec, sep_vec, after_vec)
}
// </vc-code>

}
fn main() {}