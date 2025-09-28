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
/* helper modified by LLM (iteration 3): added helper function to check if character exists in prefix */
spec fn char_in_prefix(str1: Seq<char>, idx: int, c: char) -> bool {
    exists|i: int| 0 <= i < idx && str1[i] == c
}
// </vc-helpers>

// <vc-spec>
fn first_repeated_char(str1: &Vec<char>) -> (repeated_char: Option<(usize, char)>)

    ensures
        check_first_repeated_char(str1, repeated_char),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): removed ghost variable and simplified invariants */
{
    let mut i: usize = 0;
    let n = str1.len();
    
    while i < n
        invariant
            0 <= i <= n,
            forall|j: int, k: int| 0 <= j < k < i ==> str1[j] != str1[k]
    {
        let c = str1[i];
        let mut found_in_prefix = false;
        let mut j: usize = 0;
        
        while j < i
            invariant
                0 <= j <= i,
                found_in_prefix <==> exists|k: int| 0 <= k < j && str1[k] == c
        {
            if str1[j] == c {
                found_in_prefix = true;
                break;
            }
            j += 1;
        }
        
        if found_in_prefix {
            return Some((i, c));
        }
        i += 1;
    }
    None
}
// </vc-code>

}
fn main() {}