use vstd::prelude::*;

verus! {

// The order of the recursion in these two functions
// must match the order of the iteration in the algorithm above
spec fn min_seq(a: Seq<int>) -> int
    recommends a.len() > 0
    decreases a.len() when a.len() > 0
{
    if a.len() == 1 {
        a[0]
    } else {
        let prefix = a.subrange(0, a.len() - 1);
        assume(prefix.len() < a.len());
        let min_prefix = min_seq(prefix);
        if a[a.len() - 1] <= min_prefix {
            a[a.len() - 1]
        } else {
            min_prefix
        }
    }
}

spec fn max_seq(a: Seq<int>) -> int
    recommends a.len() > 0
    decreases a.len() when a.len() > 0
{
    if a.len() == 1 {
        a[0]
    } else {
        let prefix = a.subrange(0, a.len() - 1);
        assume(prefix.len() < a.len());
        let max_prefix = max_seq(prefix);
        if a[a.len() - 1] >= max_prefix {
            a[a.len() - 1]
        } else {
            max_prefix
        }
    }
}

// <vc-helpers>
proof fn lemma_min_seq_prefix(a: Seq<int>, i: int)
    requires
        0 < i <= a.len(),
    ensures
        min_seq(a.subrange(0, i)) <= min_seq(a),
    decreases a.len()
{
    if i == a.len() {
        assert(a.subrange(0, i) == a);
    } else {
        let prefix = a.subrange(0, a.len() - 1);
        lemma_min_seq_prefix(prefix, i);
        if a[a.len() - 1] <= min_seq(prefix) {
            assert(min_seq(a) == a[a.len() - 1]);
        } else {
            assert(min_seq(a) == min_seq(prefix));
        }
    }
}

proof fn lemma_max_seq_prefix(a: Seq<int>, i: int)
    requires
        0 < i <= a.len(),
    ensures
        max_seq(a.subrange(0, i)) <= max_seq(a),
    decreases a.len()
{
    if i == a.len() {
        assert(a.subrange(0, i) == a);
    } else {
        let prefix = a.subrange(0, a.len() - 1);
        lemma_max_seq_prefix(prefix, i);
        if a[a.len() - 1] >= max_seq(prefix) {
            assert(max_seq(a) == a[a.len() - 1]);
        } else {
            assert(max_seq(a) == max_seq(prefix));
        }
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn sum_min_max(a: &[i32]) -> (sum: i32)
    requires a.len() > 0
    ensures sum == max_seq(a@.map(|i: int, x: i32| x as int)) + min_seq(a@.map(|i: int, x: i32| x as int))
// </vc-spec>
// </vc-spec>

// <vc-code>
fn sum_min_max(a: &[i32]) -> (sum: i32)
    requires a.len() > 0
    ensures sum == max_seq(a@.map(|i: int, x: i32| x as int)) + min_seq(a@.map(|i: int, x: i32| x as int))
{
    let mut min_val = a[0];
    let mut max_val = a[0];
    let mut i = 1;

    while i < a.len()
        invariant
            1 <= i <= a.len(),
            min_val == min_seq(a@.subrange(0, i as int).map(|i: int, x: i32| x as int)),
            max_val == max_seq(a@.subrange(0, i as int).map(|i: int, x: i32| x as int)),
    {
        if a[i] < min_val {
            min_val = a[i];
        }
        if a[i] > max_val {
            max_val = a[i];
        }
        i = i + 1;
    }

    assert(a@.subrange(0, a.len() as int) == a@);
    min_val + max_val
}
// </vc-code>

fn main() {}

}