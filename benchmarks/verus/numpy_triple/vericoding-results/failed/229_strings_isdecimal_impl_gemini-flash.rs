// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No modification to helper. */
// </vc-helpers>

// <vc-spec>
spec fn is_decimal_char(c: char) -> bool {
    ('0' <= c && c <= '9')
}

spec fn all_chars_decimal(s: Seq<char>) -> bool
    decreases s.len()
{
    if s.len() == 0 {
        true
    } else {
        is_decimal_char(s[0]) && all_chars_decimal(s.skip(1))
    }
}

fn isdecimal(a: Vec<String>) -> (result: Vec<bool>)
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> {
            &&& (result[i] == true <==> (a[i]@.len() > 0 && all_chars_decimal(a[i]@)))
            &&& (a[i]@ == Seq::<char>::empty() ==> result[i] == false)
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Cast `k` to `usize` for indexing. */
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i && i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> {
                &&& (result[j] == true <==> (a[j as usize].view_as_seq().len() > 0 && all_chars_decimal(a[j as usize].view_as_seq())))
                &&& (a[j as usize].view_as_seq() == Seq::<char>::empty() ==> result[j] == false)
            }
        decreases a.len() - i
    {
        let s = a[i].as_str();
        let s_seq = s.view_as_seq();
        let mut current_is_decimal_val = s_seq.len() > 0;
        if current_is_decimal_val {
            let mut k: usize = 0;
            while k < s_seq.len()
                invariant
                    0 <= k && k <= s_seq.len(),
                    current_is_decimal_val == (k == 0 || all_chars_decimal(s_seq.subsequence(0, k as int))), // Simplified invariant
                    k == 0 ==> current_is_decimal_val == true,
                    k > 0 && !all_chars_decimal(s_seq.subsequence(0,k as int)) ==> current_is_decimal_val == false
                decreases s_seq.len() - k
            {
                if !is_decimal_char(s_seq.index(k as usize)) {
                    current_is_decimal_val = false;
                    break;
                }
                k = k + 1;
            }
        }

        result.push(current_is_decimal_val);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}