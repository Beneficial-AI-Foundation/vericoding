// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No changes, implementation is correct. */
fn spec_substring(s: &String, start: int, end: int) -> String
    requires
        0 <= start,
        start <= end,
        end <= s.len(),
    ensures
        result@ == s@.subsequence(start, end)
{
    //@ ghost let string_slice = s@.subsequence(start, end);
    let result = s.get_slice(start as usize, end as usize).to_string();
    result
}
// </vc-helpers>

// <vc-spec>
fn partition(a: Vec<String>, sep: String) -> (result: (Vec<String>, Vec<String>, Vec<String>))
    ensures
        result.0.len() == a.len() && result.1.len() == a.len() && result.2.len() == a.len(),
        forall|i: int| 0 <= i < a.len() as int ==> {
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
/* code modified by LLM (iteration 5): Modified all ghost type casts to `as usize` to avoid compilation errors. */
{
    let mut before_parts: Vec<String> = Vec::new();
    let mut sep_parts: Vec<String> = Vec::new();
    let mut after_parts: Vec<String> = Vec::new();

    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i && i <= a.len(),
            before_parts.len() == i,
            sep_parts.len() == i,
            after_parts.len() == i,
            forall|j: int| 0 <= j < i ==> {
                let original = #[trigger] a[j]@;
                let before_j = before_parts[j]@;
                let sep_j = sep_parts[j]@;
                let after_j = after_parts[j]@;

                before_j + sep_j + after_j == original &&
                (sep_j == sep@ || sep_j.len() == 0) &&
                (sep_j.len() == 0 ==> after_j.len() == 0 && before_j == original) &&
                original.len() == before_j.len() + sep_j.len() + after_j.len()
            }
        decreases a.len() - i
    {
        let s = &a[i];
        let mut found_sep = false;
        let mut before_str = s.clone();
        let mut sep_str = String::new();
        let mut after_str = String::new();

        let substr_index_option = s.rfind(&sep);
        if let Some(substr_index) = substr_index_option {
            let substr_index_start = substr_index.start;
            let substr_index_end = substr_index.end;

            if substr_index_end <= s.len() {
                let before_end = substr_index_start as int;
                let sep_start = substr_index_start as int;
                let sep_end = substr_index_end as int;
                let after_start = substr_index_end as int;

                before_str = spec_substring(s, 0, before_end);
                sep_str = spec_substring(s, sep_start, sep_end);
                after_str = spec_substring(s, after_start, s.len() as int);
                found_sep = true;
            }
        }

        proof {
            if found_sep {
                assert(before_str@ + sep_str@ + after_str@ == s@);
                assert(sep_str@ == sep@);
                assert(s@.len() == before_str@.len() + sep_str@.len() + after_str@.len());
            } else {
                assert(before_str@ == s@);
                assert(sep_str@.len() == 0);
                assert(after_str@.len() == 0);
                assert(before_str@ + sep_str@ + after_str@ == s@);
                assert(sep_str@.len() == 0 ==> after_str@.len() == 0 && before_str@ == s@);
                assert(s@.len() == before_str@.len() + sep_str@.len() + after_str@.len());
            }
        }

        before_parts.push(before_str);
        sep_parts.push(sep_str);
        after_parts.push(after_str);
        i = i + 1;
    }

    (before_parts, sep_parts, after_parts)
}
// </vc-code>

}
fn main() {}