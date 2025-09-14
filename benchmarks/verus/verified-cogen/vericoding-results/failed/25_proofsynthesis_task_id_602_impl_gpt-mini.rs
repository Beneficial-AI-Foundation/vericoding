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
/* helper modified by LLM (iteration 2): exists_dup_from with preconditions */
fn exists_dup_from(str1: &Vec<char>, i: usize, j: usize) -> bool
    requires
        i < str1.len(),
        j <= str1.len(),
    decreases
        str1.len() - j
{
    if j >= str1.len() {
        false
    } else {
        if str1[j] == str1[i] {
            true
        } else {
            exists_dup_from(str1, i, j + 1)
        }
    }
}

/* helper modified by LLM (iteration 2): find_first_repeated_rec with precondition */
fn find_first_repeated_rec(str1: &Vec<char>, i: usize) -> Option<(usize, char)>
    requires
        i <= str1.len(),
    decreases
        str1.len() - i
{
    if i >= str1.len() {
        None
    } else {
        if exists_dup_from(str1, i, i + 1) {
            Some((i, str1[i]))
        } else {
            find_first_repeated_rec(str1, i + 1)
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn first_repeated_char(str1: &Vec<char>) -> (repeated_char: Option<(usize, char)>)

    ensures
        check_first_repeated_char(str1, repeated_char),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): use recursive helper to find first repeated char */
    let res = find_first_repeated_rec(str1, 0);
    res
}
// </vc-code>

}
fn main() {}