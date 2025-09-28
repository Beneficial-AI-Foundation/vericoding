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
proof fn sum_empty(xs: Seq<i32>)
    ensures sum(xs.subrange(0, 0)) == 0int
{
    let ys = xs.subrange(0, 0);
    assert(ys.len() == 0);
    assert(sum(ys) == 0int);
}

proof fn sum_subrange_push(xs: Seq<i32>, i: nat)
    requires i < xs.len()
    ensures sum(xs.subrange(0, i + 1)) == sum(xs.subrange(0, i)) + xs[i] as int
{
    let ys = xs.subrange(0, i + 1);
    assert(ys.len() == i + 1);
    assert(ys.len() > 0);
    assert(ys.len() - 1 == i);
    assert(ys.subrange(0, ys.len() - 1) =~= xs.subrange(0, i));
    assert(ys[i] == xs[i]);
    assert(sum(ys) == sum(ys.subrange(0, ys.len() - 1)) + ys[ys.len() - 1] as int);
    assert(sum(xs.subrange(0, i + 1)) == sum(xs.subrange(0, i)) + xs[i] as int);
}
// </vc-helpers>

// <vc-spec>
fn sum_array(xs: &[i32]) -> (s: i32)
    ensures s as int == sum(xs@)
// </vc-spec>
// <vc-code>
{
    let n = xs.len();
    let mut i: usize = 0;
    let mut acc: i32 = 0;

    proof {
        // Base case: prefix of length 0 sums to 0
        sum_empty(xs@);
        assert(acc as int == sum(xs@.subrange(0, 0)));
    }

    while i < n
        invariant
            i <= xs.len(),
            acc as int == sum(xs@.subrange(0, i as nat)),
    {
        let xi = xs[i];

        proof {
            // sum over prefix extended by one element
            assert(i < xs.len());
            sum_subrange_push(xs@, i as nat);
        }

        acc = acc + xi;
        i += 1;

        proof {
            // After the update, the accumulator matches the sum over the extended prefix
            assert(acc as int == sum(xs@.subrange(0, i as nat)));
        }
    }

    proof {
        assert(xs@.subrange(0, xs.len()) =~= xs@);
        assert(acc as int == sum(xs@));
    }

    acc
}
// </vc-code>

fn main() {
}

}