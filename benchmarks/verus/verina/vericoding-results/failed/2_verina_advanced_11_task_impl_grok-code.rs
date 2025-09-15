// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(x: i32, lst: Seq<i32>) -> nat {
    lst.filter(|y: i32| y == x).len()
}
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 4): Fixed typo 'chicken' to 'for' in loop declaration to resolve compilation error, and ensured invariant clause uses proper Verus syntax */
    if lst.len() == 0 {
        return -1;
    }

    let mut count: int = 0;
    let mut candidate: i32 = 0;

    for i in 0..lst.len()
        invariant
            count >= 0 &&
            count <= (i + 1) as int &&
            i >= 0 &&
            i <= lst.len() as int
    {
        if count == 0 {
            candidate = lst@[i as int];
            count = 1;
        } else if lst@[i as int] == candidate {
            count += 1;
        } else {
            count -= 1;
        }
    }

    if count == 0 {
        return -1;
    }

    // Second pass to verify
    let mut actual_count: int = 0;
    for i in 0..lst.len()
        invariant
            actual_count >= 0 &&
            actual_count <= (i + 1) as int &&
            i >= 0 &&
            i <= lst.len() as int
    {
        if lst@[i as int] == candidate {
            actual_count += 1;
        }
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