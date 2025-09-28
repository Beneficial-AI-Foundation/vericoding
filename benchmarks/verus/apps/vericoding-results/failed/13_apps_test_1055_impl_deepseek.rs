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

/* helper modified by LLM (iteration 5): Remove unsorted_length_sorted and provide proper spec functions */
spec fn max(a: int, b: int) -> int {
    if a > b { a } else { b }
}

spec fn sorted_subsequence_length(x: Seq<int>) -> int
    recommends x.len() > 0
    ensures
        result >= 0,
        is_sorted(x.subrange(0, result)),
{
    let len = x.len() as int;
    if is_sorted(x) {
        len
    } else {
        let first_half = x.subrange(0, len / 2);
        let second_half = x.subrange(len / 2, len);
        let left_result = sorted_subsequence_length(first_half);
        let right_result = sorted_subsequence_length(second_half);
        if left_result > right_result { left_result } else { right_result }
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
{
    /* code modified by LLM (iteration 5): Fix variable scoping and verification */
    let len = a.len();
    if len == 1 {
        return 1;
    }
    
    let mut result = 0;
    let mut current = a[0];
    let mut count = 1;
    
    let mut i = 1;
    while i < len
        invariant
            0 <= i <= len,
            count >= 1,
            result >= 0,
            result <= len
    {
        if a[i] >= current {
            current = a[i];
            count = count + 1;
        } else {
            if count > result {
                result = count;
            }
            current = a[i];
            count = 1;
        }
        i = i + 1;
    }
    
    if count > result {
        result = count;
    }
    
    result
}
// </vc-code>


}

fn main() {}