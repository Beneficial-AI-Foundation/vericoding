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
/* helper modified by LLM (iteration 5): add contains specification wrapper */
fn contains_char(v: &Vec<char>, c: char) -> (b: bool)
    ensures
        b == exists|i: int| 0 <= i < v.len() && v[i] == c,
{
    let mut i: usize = 0;
    while i < v.len()
        invariant
            i <= v.len(),
            forall|j: int| 0 <= j < i ==> v[j] != c ==>
                !exists|k: int| 0 <= k < i && v[k] == c,
    {
        if v[i] == c {
            return true;
        }
        i += 1;
    }
    false
}
// </vc-helpers>

// <vc-spec>
fn first_repeated_char(str1: &Vec<char>) -> (repeated_char: Option<(usize, char)>)

    ensures
        check_first_repeated_char(str1, repeated_char),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): replace contains with custom implementation */
{
    let mut seen: Vec<char> = Vec::new();
    let len = str1.len();
    let mut i: usize = 0;
    while i < len
        invariant
            i <= len,
            forall|k: int| 0 <= k < i ==> count_frequency_rcr(str1@, str1[k]) <= 1,
            seen@ =~= str1@.take(i as int).filter(|x: char| count_frequency_rcr(str1@, x) <= 1)
    {
        let current_char = str1[i];
        if contains_char(&seen, current_char) {
            return Some((i, current_char));
        } else {
            proof {
                lemma_forall_check(str1@, i as nat);
            }
            seen.push(current_char);
        }
        i += 1;
    }
    None
}
// </vc-code>

}
fn main() {}