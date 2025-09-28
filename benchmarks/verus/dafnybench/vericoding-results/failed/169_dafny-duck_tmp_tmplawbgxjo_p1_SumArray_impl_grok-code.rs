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
// Empty: no additional helpers needed.
// </vc-helpers>

// <vc-spec>
fn sum_array(xs: &[i32]) -> (s: i32)
    ensures s as int == sum(xs@)
// </vc-spec>
// <vc-code>
{
    let mut s: i32 = 0;
    let mut i: usize = 0;
    while i < xs.len()
        invariant
            i as int <= xs@.len()
            s as int == sum(xs@.subrange(0, i as int))
        decreases xs@.len() - (i as int)
    {
        assert(s as int + xs[i] as int >= i32::MIN as int && s as int + xs[i] as int <= i32::MAX as int);
        s = s + xs[i];
        i += 1;
    }
    s
}
// </vc-code>

fn main() {
}

}