// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn decode_rle(lst: Vec<(char, usize)>) -> Seq<char> {
    Seq::empty()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): construct sequence of repeated chars using Seq::new with nat */
spec fn repeat_char(c: char, n: nat) -> Seq<char> {
    if n == 0 {
        Seq::empty()
    } else {
        Seq::new(n, |_| c)
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
/* code modified by LLM (iteration 5): run-length encode a vector of chars into (char, count) pairs */
{
    let mut result: Vec<(char, usize)> = Vec::new();
    if s.len() == 0 {
        result
    } else {
        let mut i: usize = 0;
        while i < s.len() {
            let c = s[i];
            let mut cnt: usize = 1;
            i += 1;
            while i < s.len() && s[i] == c {
                cnt += 1;
                i += 1;
            }
            result.push((c, cnt));
        }
        result
    }
}

// </vc-code>

}
fn main() {}