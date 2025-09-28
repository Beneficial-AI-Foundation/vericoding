// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(x: i32, lst: Seq<i32>) -> nat {
    lst.filter(|y: i32| y == x).len()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): spec fn for diff calculation in Boyer-Moore algorithm */
spec fn diff(s: Seq<i32>, cand: i32, idx: int) -> int {
    if idx == 0 {
        0
    } else {
        let prefix = s.take(idx);
        let cs = count_occurrences(cand, prefix);
        let cc = idx as nat - cs;
        cs as int - cc as int
    }
}
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
/* code modified by LLM (iteration 5): Fixed lst@ compilation issue by inlining lst@ in invariants */
{
    if lst.len() == 0 {
        return -1;
    }
    let mut candidate = lst[0];
    let mut count = 1i32;
    let mut i = 1usize;
    while i < lst.len()
        invariant
            i as int <= lst@.len() as int,
            diff(lst@, candidate, i as int) == count as int
        decreases lst@.len() as int - i as int
    {
        if count == 0 {
            candidate = lst[i];
            count = 1;
        } else if lst[i] == candidate {
            count += 1;
        } else {
            count -= 1;
        }
        i += 1;
    }
    let mut actual_count = 0usize;
    let mut j = 0usize;
    while j < lst.len()
        invariant
            j as int <= lst@.len() as int,
            actual_count as int == count_occurrences(candidate, lst@.take(j as int))
        decreases lst@.len() as int - j as int
    {
        if lst[j] == candidate {
            actual_count += 1;
        }
        j += 1;
    }
    if actual_count > lst.len() / 2 {
        candidate
    } else {
        -1
    }
}
// </vc-code>

}
fn main() {}