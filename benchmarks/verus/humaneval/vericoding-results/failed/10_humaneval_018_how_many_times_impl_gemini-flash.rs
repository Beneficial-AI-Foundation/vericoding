// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed type casting issues */
fn is_subsequence(s: Seq<char>, start: usize, substr: Seq<char>) -> (result: bool)
    requires
        start + substr.len() <= s.len(),
    ensures
        result == (s.subrange(start as int, (start + substr.len()) as int) == substr),
{
    s.subrange(start as int, (start + substr.len()) as int) == substr
}
// </vc-helpers>

// <vc-spec>
fn how_many_times(s: Vec<char>, substr: Vec<char>) -> (times: usize)
    ensures times == Set::new(|i: int| 0 <= i <= s@.len() - substr@.len() && s@.subrange(i, i + substr@.len()) == substr@).len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed type casting issue for subrange indices */
{
    let s_seq = s@;
    let substr_seq = substr@;

    if substr_seq.len() == 0 {
        return if s_seq.len() == 0 { 1 } else { s_seq.len() + 1 };
    }

    if s_seq.len() < substr_seq.len() {
        return 0;
    }

    let mut count: usize = 0;
    let mut i: usize = 0;

    let max_i = s_seq.len() - substr_seq.len();

    while i <= max_i
        invariant
            0 <= i as int,
            i <= max_i + 1,
            count == Set::new(|j: int| 0 <= j < i as int && s_seq.subrange(j, (j + substr_seq.len()) as int) == substr_seq).len(),
        decreases max_i - i
    {
        if is_subsequence(s_seq, i, substr_seq) {
            count = count + 1;
        }
        i = i + 1;
    }
    count
}
// </vc-code>


}

fn main() {}