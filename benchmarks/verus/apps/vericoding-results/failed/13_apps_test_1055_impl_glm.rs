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
/* helper modified by LLM (iteration 2): fixed map usage by using explicit subrange and casting indices to int */
fn is_sorted_exec(a: &[i8], start: usize, end: usize) -> (result: bool)
    requires 
        0 <= start < end <= a.len(),
    ensures
        result == is_sorted(a@.subrange(start as int, end as int).map(|i, x| x as int)),
{
    let mut i = start;
    while i < end - 1
        invariant 
            forall|j: int, k: int| start <= j < k <= i ==> a@[j] <= a@[k],
            start <= i <= end,
        decreases end - i
    {
        if a[i] > a[i+1] {
            return false;
        }
        i += 1;
    }
    true
}

/* helper modified by LLM (iteration 2): fixed map usage by using explicit subrange and casting indices to int */
fn thanos_sort_helper(a: &[i8], start: usize, end: usize) -> (result: usize)
    requires 
        0 <= start < end <= a.len(),
        end - start > 0,
    ensures
        result as int == thanos_sort(a@.subrange(start as int, end as int).map(|i, x| x as int)),
        1 <= result <= (end - start),
    decreases end - start
{
    if is_sorted_exec(a, start, end) {
        end - start
    } else {
        let mid = start + (end - start) / 2;
        let left = thanos_sort_helper(a, start, mid);
        let right = thanos_sort_helper(a, mid, end);
        if left > right {
            left
        } else {
            right
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
/* code modified by LLM (iteration 2): no changes needed, but helper functions were fixed */
{
    let result = thanos_sort_helper(&a, 0, a.len());
    result
}
// </vc-code>


}

fn main() {}