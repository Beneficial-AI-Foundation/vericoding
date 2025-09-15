// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn decode_rle(lst: Vec<(char, usize)>) -> Seq<char> {
    Seq::empty()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): simple spec min function retained for potential use */
spec fn min(a: int, b: int) -> int { if a < b { a } else { b } }
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
    /* code modified by LLM (iteration 3): add decreases clause for loop and keep basic RLE implementation */
    let mut result: Vec<(char, usize)> = Vec::new();
    let n = s.len();
    if n == 0 { return result; }
    let mut i: usize = 0;
    let mut current: char = s[i];
    let mut count: usize = 1;
    i += 1;
    while i < n
        decreases (n - i) as int
    {
        let ch = s[i];
        if ch == current {
            count += 1;
        } else {
            result.push((current, count));
            current = ch;
            count = 1;
        }
        i += 1;
    }
    result.push((current, count));
    result
}
// </vc-code>

}
fn main() {}