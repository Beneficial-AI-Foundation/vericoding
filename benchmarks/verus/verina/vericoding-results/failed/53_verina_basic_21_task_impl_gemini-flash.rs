// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_subseq_at(sub: Vec<i32>, main: Vec<i32>, i: int) -> bool {
    0 <= i && i + sub.len() <= main.len() && 
    (forall|j: int| 0 <= j < sub.len() ==> sub[j] == main[i + j])
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn is_sublist(sub: &Vec<i32>, main: &Vec<i32>) -> (result: bool)
    ensures
        result <==> exists|i: int| is_subseq_at(*sub, *main, i),
// </vc-spec>
// <vc-code>
{
    let sub_len = sub.len();
    let main_len = main.len();

    if sub_len == 0 {
        return true;
    }
    if sub_len > main_len {
        return false;
    }

    let mut i: int = 0;
    while i <= main_len - sub_len
        invariant
            0 <= i,
            i <= main_len - sub_len + 1,
            main_len - sub_len >= 0 ==> (forall|k: int| 0 <= k < i ==> !is_subseq_at(*sub, *main, k)),
    {
        let mut j: int = 0;
        let mut match_found = true;
        while j < sub_len
            invariant
                0 <= j,
                j <= sub_len,
                match_found == true <==> (forall|k: int| 0 <= k < j ==> sub[k] == main[i + k]),
                0 <= i,
                i + sub_len <= main_len + 1,
        {
            if sub[j] != main[i + j] {
                match_found = false;
                break;
            }
            j = j + 1;
        }

        if match_found {
            return true;
        }
        i = i + 1;
    }
    false
}
// </vc-code>

}
fn main() {}