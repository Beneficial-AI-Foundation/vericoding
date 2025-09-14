// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn has_common_element(list1: &Vec<i32>, list2: &Vec<i32>) -> (result: bool)

    ensures
        result == (exists|i: int, j: int|
            0 <= i < list1.len() && 0 <= j < list2.len() && (list1[i] == list2[j])),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): added decreases clauses to both loops */
    let mut i: usize = 0;
    while i < list1.len()
        invariant
            0 <= i <= list1.len(),
            forall|k: int, j: int| 0 <= k < i && 0 <= j < list2.len() ==> list1[k as int] != list2[j as int],
        decreases list1.len() - i,
    {
        let mut j: usize = 0;
        while j < list2.len()
            invariant
                0 <= i < list1.len(),
                0 <= j <= list2.len(),
                forall|k: int| 0 <= k < j ==> list1[i as int] != list2[k as int],
                forall|k: int, m: int| 0 <= k < i && 0 <= m < list2.len() ==> list1[k as int] != list2[m as int],
            decreases list2.len() - j,
        {
            if list1[i] == list2[j] {
                return true;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    false
}
// </vc-code>

}
fn main() {}