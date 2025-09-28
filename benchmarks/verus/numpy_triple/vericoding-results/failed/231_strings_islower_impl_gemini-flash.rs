// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No helper functions needed; the existing helpers are sufficient. */
// </vc-helpers>

// <vc-spec>
spec fn is_alpha_char(c: char) -> bool {
    ('a' <= c <= 'z') || ('A' <= c <= 'Z')
}

spec fn is_lower_char(c: char) -> bool {
    'a' <= c <= 'z'
}

spec fn string_has_cased_char(s: Seq<char>) -> bool {
    exists|i: int| 0 <= i < s.len() && is_alpha_char(s[i])
}

spec fn string_all_cased_are_lowercase(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() && is_alpha_char(s[i]) ==> is_lower_char(s[i])
}

fn islower(a: Vec<String>) -> (result: Vec<bool>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            result[i as int] == (string_has_cased_char(a[i]@) && string_all_cased_are_lowercase(a[i]@))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Correct `usize` to `nat` and `int` for indexing `s_seq` based on Verus `Seq` indexing requirements. */
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i && i <= a.len(),
            result.len() == i,
            // For all j < i, result[j] is correctly computed
            forall|j: int| 0 <= j < i ==> result[j] == (string_has_cased_char(a[j]@) && string_all_cased_are_lowercase(a[j]@)),
    {
        let s: &String = &a[i];
        let mut has_cased = false;
        let mut all_lowercase = true;

        let mut char_idx_usize: usize = 0;
        let s_seq = s@;
        while char_idx_usize < s_seq.len()
            invariant
                0 <= char_idx_usize && (char_idx_usize as nat) <= s_seq.len(),
                has_cased == (exists|k: int| 0 <= k < char_idx_usize && is_alpha_char(s_seq[k])), /* OLD SYNTAX: s_seq.index(k as nat) */
                all_lowercase == (forall|k: int| 0 <= k < char_idx_usize && is_alpha_char(s_seq[k]) ==> is_lower_char(s_seq[k])), /* OLD SYNTAX: s_seq.index(k as nat) */
        {
            let char_idx: int = char_idx_usize as int;
            let c = s_seq[char_idx];
            if is_alpha_char(c) {
                has_cased = true;
                if !is_lower_char(c) {
                    all_lowercase = false;
                }
            }
            char_idx_usize = char_idx_usize + 1;
        }

        result.push(has_cased && all_lowercase);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}