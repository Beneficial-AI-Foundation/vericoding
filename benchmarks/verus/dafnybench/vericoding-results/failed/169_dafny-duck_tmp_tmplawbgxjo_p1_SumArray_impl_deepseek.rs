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
proof fn sum_empty() 
    ensures sum(Seq::empty()) == 0
{
}

proof fn sum_recursive(xs: Seq<i32>, i: int)
    requires
        0 <= i <= xs.len(),
    ensures
        sum(xs.subrange(0, i)) == if i == 0 {
            0
        } else {
            sum(xs.subrange(0, i - 1)) + xs[i - 1] as int
        }
    decreases i
{
    if i == 0 {
        assert(sum(Seq::empty()) == 0);
    } else {
        let prev = i - 1;
        assert(0 <= prev <= xs.len());
        sum_recursive(xs, prev);
        assert(xs.subrange(0, i) == xs.subrange(0, prev).push(xs[prev]));
        assert(sum(xs.subrange(0, i)) == sum(xs.subrange(0, prev)) + xs[prev] as int);
    }
}

proof fn sum_nonnegative(xs: Seq<i32>)
    ensures
        sum(xs) >= 0,
    decreases xs.len()
{
    if xs.len() > 0 {
        let prev = xs.len() - 1;
        sum_nonnegative(xs.subrange(0, prev));
        assert(sum(xs) == sum(xs.subrange(0, prev)) + xs[prev] as int);
    }
}
// </vc-helpers>

// <vc-spec>
fn sum_array(xs: &[i32]) -> (s: i32)
    ensures s as int == sum(xs@)
// </vc-spec>
// <vc-code>
{
    let mut s: i32 = 0;
    let mut idx: usize = 0;
    let n = xs.len();
    while idx < n
        invariant
            0 <= idx <= n,
            s as int == sum(xs@.subrange(0, idx as int)),
        decreases n - idx
    {
        proof {
            sum_recursive(xs@, (idx + 1) as int);
        }
        assert(0 <= idx < xs@.len());
        let old_s = s;
        s = s + xs[idx];
        proof {
            assert(old_s as int == sum(xs@.subrange(0, idx as int)));
            assert((old_s + xs[idx]) as int == old_s as int + xs[idx] as int);
            assert(sum(xs@.subrange(0, (idx + 1) as int)) == sum(xs@.subrange(0, idx as int)) + xs@[idx as int] as int);
        }
        idx = idx + 1;
        proof {
            assert(s as int == sum(xs@.subrange(0, idx as int)));
        }
    }
    s
}
// </vc-code>

fn main() {
}

}