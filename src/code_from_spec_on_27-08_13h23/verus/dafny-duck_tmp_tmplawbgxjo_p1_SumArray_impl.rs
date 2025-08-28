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
proof fn sum_non_negative(xs: Seq<i32>)
    requires forall|i: int| 0 <= i < xs.len() ==> xs[i] >= 0,
    ensures sum(xs) >= 0,
    decreases xs.len()
{
    if xs.len() == 0 {
        assert(sum(xs) == 0);
    } else {
        sum_non_negative(xs.subrange(0, xs.len() - 1));
        assert(sum(xs) == sum(xs.subrange(0, xs.len() - 1)) + xs[xs.len() - 1] as int);
        assert(sum(xs) >= 0);
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn sum_array(xs: &[i32]) -> (s: i32)
    ensures s as int == sum(xs@)
// </vc-spec>
// </vc-spec>

// <vc-code>
fn sum_array(xs: &[i32]) -> (s: i32)
    ensures s as int == sum(xs@)
{
    let mut total: i32 = 0;
    let mut i: usize = 0;
    while i < xs.len()
        invariant
            0 <= i <= xs.len(),
            total as int == sum(xs@.subrange(0, i as int))
    {
        total = total + xs[i];
        i = i + 1;
    }
    total
}
// </vc-code>

fn main() {
}

}