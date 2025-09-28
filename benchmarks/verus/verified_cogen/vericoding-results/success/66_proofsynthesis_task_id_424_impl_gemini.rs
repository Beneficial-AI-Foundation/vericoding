// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn extract_rear_chars(s: &Vec<Vec<char>>) -> (result: Vec<char>)

    requires
        forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i].len() > 0,

    ensures
        s.len() == result.len(),
        forall|i: int| 0 <= i < s.len() ==> result[i] == #[trigger] s[i][s[i].len() - 1],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): added invariant to carry over the precondition about inner vector lengths */
    let mut result: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            result.len() == i,
            forall|k: int| 0 <= k < s.len() ==> s@[k].len() > 0,
            forall|j: int| 0 <= j < i ==> result@[j] == s@[j]@[s@[j].len() - 1],
        decreases s.len() - i
    {
        result.push(s[i][s[i].len() - 1]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}