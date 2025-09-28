use vstd::prelude::*;

verus! {

// Given an array of integers, it returns the sum. [1,3,3,2]->9

spec fn sum(xs: Seq<i32>) -> int
    decreases xs.len()
{
    if xs.len() == 0 {
        0int
    } else {
        sum(xs.subrange(0, xs.len() - 1)) + xs[xs.len() - 1] as int
    }
}

// <vc-helpers>
fn sum_array_helper(xs: &[i32], start_index: usize) -> (s: i32)
    requires
        start_index <= xs.len(),
    ensures
        s as int == sum(xs@.subrange(start_index as nat, xs.len() as nat)),
{
    if start_index == xs.len() {
        0
    } else {
        let element = xs[start_index];
        let remaining_sum = sum_array_helper(xs, start_index + 1);
        
        proof {
            assert(sum(xs@.subrange(start_index as nat, xs.len() as nat)) == element as int + sum(xs@.subrange( (start_index + 1) as nat, xs.len() as nat)));
        }
        
        element + remaining_sum
    }
}
// </vc-helpers>

// <vc-spec>
fn sum_array(xs: &[i32]) -> (s: i32)
    ensures s as int == sum(xs@)
// </vc-spec>
// <vc-code>
{
    let mut current_sum: i32 = 0;
    let mut i: usize = 0;

    while i < xs.len()
        invariant
            0 <= i,
            i <= xs.len(),
            current_sum as int == sum(xs@.subrange(0, i as nat)),
    {
        current_sum = current_sum + xs[i];
        i = i + 1;
    }
    current_sum
}
// </vc-code>

fn main() {
}

}