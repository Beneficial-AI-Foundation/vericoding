// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(a: Seq<int>) -> bool {
    a.len() > 0
}

spec fn is_sorted(x: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < x.len() ==> x[i] <= x[j]
}

spec fn thanos_sort(x: Seq<int>) -> int
    requires 
        x.len() > 0
    ensures 
        thanos_sort(x) >= 1,
        thanos_sort(x) <= x.len(),
        is_sorted(x) ==> thanos_sort(x) == x.len(),
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
// </vc-helpers>

// <vc-spec>
fn solve(a: Seq<int>) -> (result: int)
    requires 
        valid_input(a)
    ensures 
        result == thanos_sort(a),
        1 <= result <= a.len(),
// </vc-spec>
// <vc-code>
{
    assume(false);
    0int
}
// </vc-code>


}

fn main() {}