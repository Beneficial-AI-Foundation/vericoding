// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn decode_rle(lst: Vec<(char, usize)>) -> Seq<char> {
    Seq::empty()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): add type conversions for subrange */
spec fn decode_rle_internal(lst: Seq<(char, nat)>) -> Seq<char>
{
    if lst.len() == 0 {
        Seq::empty()
    } else {
        let head = lst[0];
        let mut s = Seq::empty();
        let num_reps: nat = head.1;
        let ch: char = head.0;
        let mut i: nat = 0;
        while i < num_reps {
            s = s.push(ch);
            i = i + 1;
        }
        s + decode_rle_internal(lst.subrange(1, lst.len() as int))
    }
}
// </vc-helpers>

// <vc-spec>
fn run_length_encode(s: &Vec<char>) -> (result: Vec<(char, usize)>)
    ensures
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i].1 > 0,
        forall|i: int| 0 <= i < result.len() ==> i + 1 < result.len() ==> #[trigger] result[i].0 != result[i + 1].0,
        decode_rle(result) == s@,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): [brief description] */
{
    let mut result: Vec<(char, usize)> = Vec::new();
    let mut i: usize = 0;

    while i < s.len()
        invariant
            0 <= i && i <= s.len(),
            result.len() <= s.len(),
            forall|k: int| 0 <= k < result.len() ==> result[k].1 > 0,
            forall|k: int| 0 <= k < result.len() ==> k + 1 < result.len() ==> result[k].0 != result[k + 1].0,
            // TODO: Add more invariants to relate result to s
        decreases (s.len() - i)
    {
        let current_char = s[i];
        let mut count: usize = 0;
        let mut j: usize = i;

        while j < s.len() && s[j] == current_char
            invariant
                0 <= j && j <= s.len(),
                0 <= count && count <= s.len(),
                count == (j - i),
                j >= i,
                forall|k: int| i <= k < j ==> s[k] == current_char,
            decreases (s.len() - j)
        {
            j = j + 1;
            count = count + 1;
        }

        result.push((current_char, count));
        i = j;
    }

    result
}
// </vc-code>

}
fn main() {}