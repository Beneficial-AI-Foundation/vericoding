// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn decode_rle(lst: Vec<(char, usize)>) -> Seq<char> {
    Seq::empty()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed multiple definition error for decode_rle; changed input lst to Seq to match Verus specs */
spec fn decode_rle_spec(lst: Seq<(char, usize)>) -> Seq<char>
{
    let mut decoded = Seq::empty();
    let mut idx = 0;
    while idx < lst.len()
        invariant (
            0 <= idx && idx <= lst.len(),
            decoded.len() <= lst.map_values(|(c, count)| count as int).sum(),
        )
    {
        let (c, count) = lst[idx];
        let mut i = 0;
        while i < count
            invariant (
                0 <= i && i <= count,
                decoded.len() <= lst.map_values(|(c, count)| count as int).sum(),
            )
        {
            decoded = decoded.push(c);
            i = i + 1;
        }
        idx = idx + 1;
    }
    decoded
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
/* code modified by LLM (iteration 5): updated decode_rle call to decode_rle_spec */
{
    let mut result: Vec<(char, usize)> = Vec::new();
    let mut i: usize = 0;

    while i < s.len()
        invariant (
            0 <= i && i <= s.len() as int,
            forall|j: int| 0 <= j < result.len() ==> result[j].1 > 0,
            forall|j: int| 0 <= j < result.len() ==> j + 1 < result.len() ==> result[j].0 != result[j + 1].0,
            decode_rle_spec(result@) == s@.subsequence(0, i as int),
        )
        decreases s.len() - i
    {
        let current_char = s[i];
        let mut count: usize = 0;
        let mut j: usize = i;

        while j < s.len() && s[j] == current_char
            invariant (
                i <= j && j <= s.len() as int,
                count == (j - i),
                forall|k: int| i <= k < j ==> s[k] == current_char,
            )
            decreases s.len() - j
        {
            count = count + 1;
            j = j + 1;
        }

        result.push((current_char, count));
        i = j;
    }
    result
}
// </vc-code>

}
fn main() {}