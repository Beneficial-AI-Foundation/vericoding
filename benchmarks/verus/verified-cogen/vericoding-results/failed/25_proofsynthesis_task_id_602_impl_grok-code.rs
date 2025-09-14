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
proof fn count_frequency_up_to_index(str: &Vec<char>, idx: int, key: char) -> (result: int)
    requires 0 <= idx <= str.len()
    ensures result == count_frequency_rcr(str@.take(idx), key)
    decreases idx,
{
    if idx == 0 {
        0
    } else {
        count_frequency_up_to_index(str, idx - 1, key) + if (str@[idx - 1] == key) { 1int } else { 0int }
    }
}
/* helper modified by LLM (iteration 5): Added int type annotations for literals to resolve compilation errors */
// </vc-helpers>

// <vc-spec>
fn first_repeated_char(str1: &Vec<char>) -> (repeated_char: Option<(usize, char)>)

    ensures
        check_first_repeated_char(str1, repeated_char),
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 5): Changed i to usize type, cast to int for Seq operations, and simplified invariant to avoid forall type errors */
    let mut seen: Seq<char> = Seq::empty();
    let mut i: usize = 0;
    while i < str1.len()
        invariant
            i <= str1.len(),
            seen.len() == (i as int),
            seen == str1@.take(i as int),
            seen.no_duplicates(),
    {
        let current = str1@[i];
        if seen.contains(current) {
            return Some((i, current));
        } else {
            seen = seen.push(current);
        }
        i += 1;
        proof {
            assert(seen.no_duplicates());
        }
    }
    None
}
// </vc-code>

}
fn main() {}