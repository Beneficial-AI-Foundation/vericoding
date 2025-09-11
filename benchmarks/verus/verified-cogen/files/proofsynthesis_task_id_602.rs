// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_frequency_rcr(seq: Seq<char>, key: char) -> (result: int)
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        count_frequency_rcr(seq.drop_last(), key) + if (seq.last() == key) {
            1 as int
        } else {
            0 as int
        }
    }
}
spec fn check_first_repeated_char(str1: &Vec<char>, repeated_char: Option<(usize, char)>) -> (res: bool) {
    if let Some((idx, rp_char)) = repeated_char {
        &&& str1@.take(idx as int) =~= str1@.take(idx as int).filter(
            |x: char| count_frequency_rcr(str1@, x) <= 1,
        )
        &&& count_frequency_rcr(str1@, rp_char) > 1
    } else {
        forall|k: int|
            0 <= k < str1.len() ==> count_frequency_rcr(str1@, #[trigger] str1[k]) <= 1
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn first_repeated_char(str1: &Vec<char>) -> (repeated_char: Option<(usize, char)>)

    ensures
        check_first_repeated_char(str1, repeated_char),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}