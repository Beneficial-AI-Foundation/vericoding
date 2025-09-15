// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(x: i32, lst: Seq<i32>) -> nat {
    lst.filter(|y: i32| y == x).len()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): provide seq_len helper */
spec fn seq_len(lst: Seq<i32>) -> nat { lst.len() }
// </vc-helpers>

// <vc-spec>
fn find_majority_element(lst: &Vec<i32>) -> (result: i32)
    ensures ({
        let lst_seq = lst@;
        let n = lst_seq.len();
        let majority = count_occurrences(result, lst_seq) > n / 2 && 
                      forall|x: i32| count_occurrences(x, lst_seq) <= n / 2 || x == result;
        (result == -1 ==> forall|x: i32| count_occurrences(x, lst_seq) <= n / 2) &&
        (result != -1 ==> majority)
    })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Boyer-Moore two-pass majority vote with combined invariants */
    let n: nat = lst@.len();
    if n == 0 {
        -1
    } else {
        let mut count: int = 0;
        let mut candidate: i32 = 0;
        let mut idx: nat = 0;
        while idx < n
            invariant idx <= n
            decreases n - idx
        {
            let val: i32 = lst[idx as usize];
            if count == 0 {
                candidate = val;
                count = 1;
            } else if candidate == val {
                count = count + 1;
            } else {
                count = count - 1;
            }
            idx = idx + 1;
        }
        let mut occ: nat = 0;
        let mut j: nat = 0;
        while j < n
            invariant j <= n && occ <= n
            decreases n - j
        {
            if lst[j as usize] == candidate {
                occ = occ + 1;
            }
            j = j + 1;
        }
        if occ * 2 > n {
            candidate
        } else {
            -1
        }
    }
}
// </vc-code>

}
fn main() {}