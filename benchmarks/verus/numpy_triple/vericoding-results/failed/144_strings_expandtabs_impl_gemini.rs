// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed a compilation error by changing character-indexed string iteration to byte-indexed iteration, which is compatible with executable code. */
fn expand_one(s: String, tab_size: usize) -> (result: String)
    requires
        tab_size > 0,
    ensures
        !result.view().contains('\t'),
        !s.view().contains('\t') ==> result.view() == s.view(),
        result.view().len() >= s.view().len(),
        s.view().contains('\t') ==> result.view().len() > s.view().len(),
{
    if !s.view().contains('\t') {
        return s;
    }

    let mut result_string = String::new();
    let mut i: usize = 0;

    let num_spaces = if tab_size == 1 { 2 } else { tab_size };
    proof {
        if tab_size > 1 {
            assert(num_spaces == tab_size);
        } else {
            assert(tab_size == 1);
            assert(num_spaces == 2);
        }
        assert(num_spaces > 1);
    }

    while i < s.len()
        invariant
            0 <= i <= s.len(),
            s.is_char_boundary(i),
            s.view().contains('\t'),
            num_spaces == (if tab_size == 1 { 2 } else { tab_size }),
            num_spaces > 1,
            !result_string.view().contains('\t'),
            let processed_char_count = s.char_index_at_byte(i),
            let processed_s_view = s.view().subrange(0, processed_char_count),
            result_string.view().len() >= processed_s_view.len(),
            (!processed_s_view.contains('\t')) ==> (result_string.view().len() == processed_s_view.len()),
            (processed_s_view.contains('\t')) ==> (result_string.view().len() > processed_s_view.len()),
    {
        let (c, next_i) = s.get_char_utf8(i);

        if c == '\t' {
            let old_len = result_string.view().len();
            let mut k: usize = 0;
            while k < num_spaces
                invariant
                    0 <= k <= num_spaces,
                    !result_string.view().contains('\t'),
                    result_string.view().len() == old_len + (k as nat),
            {
                result_string.push(' ');
                k = k + 1;
            }
        } else {
            result_string.push(c);
        }
        i = next_i;
    }
    result_string
}
// </vc-helpers>

// <vc-spec>
fn expandtabs(a: Vec<String>, tabsize: Vec<usize>) -> (result: Vec<String>)
    requires 
        a.len() == tabsize.len(),
        forall|i: int| 0 <= i < tabsize.len() ==> tabsize[i] > 0,
    ensures
        result.len() == a.len(),
        forall|i: int| #![trigger result[i]] 0 <= i < result.len() ==> {
            let orig_str = &a[i];
            let result_str = &result[i];
            let tab_sz = tabsize[i];

            (forall|c: char| result_str@.contains(c) ==> c != '\t') &&

            (!orig_str@.contains('\t') ==> result_str@ == orig_str@) &&

            (result_str@.len() >= orig_str@.len()) &&

            (orig_str@.contains('\t') ==> result_str@.len() > orig_str@.len())
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): No changes were needed in this section as the compilation error was in the helper function. */
{
    let mut result: Vec<String> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            a.len() == tabsize.len(),
            result.len() == i,
            forall|j: int| 0 <= j < tabsize.len() ==> tabsize[j] > 0,
            forall|j: int| #![trigger result[j]] 0 <= j < i ==> {
                let orig_str = &a[j];
                let result_str = &result[j];
                let tab_sz = tabsize[j];
                (forall|c: char| result_str@.contains(c) ==> c != '\t') &&
                (!orig_str@.contains('\t') ==> result_str@ == orig_str@) &&
                (result_str@.len() >= orig_str@.len()) &&
                (orig_str@.contains('\t') ==> result_str@.len() > orig_str@.len())
            }
    {
        let s = a[i].clone();
        let ts = tabsize[i];
        let expanded_s = expand_one(s, ts);
        result.push(expanded_s);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}