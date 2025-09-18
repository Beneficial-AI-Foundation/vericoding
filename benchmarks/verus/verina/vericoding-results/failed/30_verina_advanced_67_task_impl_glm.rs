// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn decode_rle(lst: Vec<(char, usize)>) -> Seq<char> {
    Seq::empty()
}
// </vc-preamble>

// <vc-helpers>
spec fn make_sequence(c: char, n: usize) -> Seq<char> {
    Seq::new(|i: int| 0 <= i < n as int, |i: int| c)
}

/* helper modified by LLM (iteration 4): fixed type from SeqSeq<T> to Seq<Seq<T>> */
spec fn concat<T>(seqs: Seq<Seq<T>>) -> Seq<T>
    decreases seqs.len(),
{
    if seqs.len() == 0 {
        Seq::empty()
    } else {
        seqs[0] + concat(seqs.skip(1))
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
{
    /* code modified by LLM (iteration 4): no changes (helper compilation error fixed) */
    let mut result: Vec<(char, usize)> = Vec::new();
    if s.len() == 0 {
        return result;
    }
    let mut current_char = s[0];
    let mut count: usize = 1;
    for i in 1..s.len() {
        if s[i] == current_char {
            count = count + 1;
        } else {
            result.push((current_char, count));
            current_char = s[i];
            count = 1;
        }
    }
    result.push((current_char, count));
    result
}
// </vc-code>

}
fn main() {}