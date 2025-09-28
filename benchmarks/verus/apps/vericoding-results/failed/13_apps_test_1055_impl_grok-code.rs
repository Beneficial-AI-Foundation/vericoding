// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(a: Seq<int>) -> bool {
    a.len() > 0
}

spec fn is_sorted(x: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < x.len() ==> x[i] <= x[j]
}

spec fn thanos_sort(x: Seq<int>) -> int
    recommends x.len() > 0
    decreases x.len()
{
    let len = x.len() as int;
    if is_sorted(x) {
        len
    } else {
        let first_half = x.subrange(0, len / 2);
        let second_half = x.subrange(len / 2, len);
        let left_result = thanos_sort(first_half);
        let right_result = thanos_sort(second_half);
        if left_result > right_result { left_result } else { right_result }
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed indexing by casting usize to int for sequence access */
fn thanos_helper(a: &Vec<i8>, start: usize, end: usize) -> (result: usize)
    requires
        start <= end <= a.len(),
        valid_input(a@.map(|i: int, x: i8| x as int)),
    ensures
        start < end ==> 1 <= result as int && result <= end - start as int,
        result as int == thanos_sort(a@.map(|i: int, x: i8| x as int).subrange(start as int, end as int)),
    decreases end - start
{
    let len = end - start;
    if len <= 1 {
        len
    } else {
        let mut sorted = true;
        let mut i = start + 1;
        while i < end
            invariant
                start <= i <= end,
                sorted == (forall|k: int| (start as int) <= k < (i as int) ==> a@[k] <= a@[k+1]),
            decreases end - i
        {
            if a@((i - 1) as int) > a@(i as int) {
                sorted = false;
                break;
            }
            i += 1;
        }
        if sorted {
            len
        } else {
            let mid = (start + end) / 2;
            let left = thanos_helper(a, start, mid);
            let right = thanos_helper(a, mid, end);
            if left > right { left } else { right }
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(a: Vec<i8>) -> (result: usize)
    requires 
        valid_input(a@.map(|i, x| x as int)),
    ensures 
        result as int == thanos_sort(a@.map(|i, x| x as int)),
        1 <= result <= a.len(),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): unchanged, as helper fix suffices */
{
    if a.len() == 0 {
        1
    } else {
        thanos_helper(&a, 0, a.len())
    }
}
// </vc-code>


}

fn main() {}