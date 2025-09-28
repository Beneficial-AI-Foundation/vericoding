// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No helpers provided as they are already defined in the Verus spec block. */
// </vc-helpers>

// <vc-spec>
spec fn is_alpha_char(c: char) -> bool {
    ('A' <= c && c <= 'Z') || ('a' <= c && c <= 'z')
}

spec fn string_is_alpha(s: Seq<char>) -> bool {
    s.len() > 0 && forall|i: int| 0 <= i < s.len() ==> is_alpha_char(s[i])
}

fn is_alpha(input: Vec<String>) -> (ret: Vec<bool>)
    ensures
        ret.len() == input.len(),
        forall|i: int| 0 <= i < input.len() ==> 
            ret[i] == string_is_alpha(input[i]@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected `char_at` argument type from `nat` to `int` based on new Verus behavior, and removed unnecessary `as nat` cast. */
{
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;

    while i < input.len()
        invariant
            0 <= i as int,
            i as int <= input.len() as int,
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> result[j] == string_is_alpha(input[j as usize]@),
        decreases input.len() - i
    {
        let s = &input[i];
        let mut current_string_is_alpha: bool = false;

        if s.len() > 0 {
            let mut all_alpha = true;
            let mut k: usize = 0;
            while k < s.len()
                invariant
                    0 <= k as int,
                    k as int <= s.len() as int,
                    all_alpha ==> forall|l: int| 0 <= l < k as int ==> is_alpha_char(s@.char_at(l as int)),
                decreases s.len() - k
            {
                let char_at_k: char = s@.char_at(k as int);
                if !is_alpha_char(char_at_k) {
                    all_alpha = false;
                }
                k = k + 1;
            }
            current_string_is_alpha = all_alpha;
        }

        result.push(current_string_is_alpha);
        i = i + 1;
    }

    result
}
// </vc-code>


}
fn main() {}