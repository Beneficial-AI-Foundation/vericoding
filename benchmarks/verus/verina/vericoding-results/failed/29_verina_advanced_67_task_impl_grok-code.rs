// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn decode_rle(lst: Vec<(char, usize)>) -> Seq<char> {
    Seq::empty()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fix decode_rle spec function with loop to build sequence */
spec fn decode_rle(lst: Vec<(char, usize)>) -> Seq<char> {
    let mut res = Seq::<char>::empty();
    for i in 0..lst.len() {
        res = res + Seq::new(lst[i].0, lst[i].1 as int);
    }
    res
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
{
/* code modified by LLM (iteration 5): implement run length encoding with loop and invariant using decode_rle */
    let mut result = Vec::new();
    if s.len() == 0 {
        return result;
    }
    let mut current_char = s[0];
    let mut current_count = 1;
    let mut i = 1;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            current_count > 0,
            current_count < usize::MAX,
            #[trigger] decode_rle(result) + Seq::new(current_char, current_count as int) == s@[0..i]
        decreases s.len() - i
    {
        if s[i] == current_char {
            current_count = current_count + 1;
        } else {
            result.push((current_char, current_count));
            current_char = s[i];
            current_count = 1;
        }
        i = i + 1;
    }
    result.push((current_char, current_count));
    result
}
// </vc-code>

}
fn main() {}