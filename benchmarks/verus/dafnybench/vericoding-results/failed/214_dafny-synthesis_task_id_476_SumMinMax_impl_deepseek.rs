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
proof fn min_seq_nonempty(a: Seq<int>, i: int)
    requires
        a.len() > 0,
        0 <= i < a.len(),
    ensures
        min_seq(a) <= a[i],
    decreases a.len()
{
    if a.len() == 1 {
        assert(a[i] == a[0]);
    } else {
        let prefix = a.subrange(0, a.len() - 1);
        if i < a.len() - 1 {
            min_seq_nonempty(prefix, i);
            assert(min_seq(a) == if a[a.len() - 1] <= min_seq(prefix) { a[a.len() - 1] } else { min_seq(prefix) });
        } else {
            assert(i == a.len() - 1);
            assert(min_seq(a) == if a[a.len() - 1] <= min_seq(prefix) { a[a.len() - 1] } else { min_seq(prefix) });
        }
    }
}

proof fn max_seq_nonempty(a: Seq<int>, i: int)
    requires
        a.len() > 0,
        0 <= i < a.len(),
    ensures
        max_seq(a) >= a[i],
    decreases a.len()
{
    if a.len() == 1 {
        assert(a[i] == a[0]);
    } else {
        let prefix = a.subrange(0, a.len() - 1);
        if i < a.len() - 1 {
            max_seq_nonempty(prefix, i);
            assert(max_seq(a) == if a[a.len() - 1] >= max_seq(prefix) { a[a.len() - 1] } else { max_seq(prefix) });
        } else {
            assert(i == a.len() - 1);
            assert(max_seq(a) == if a[a.len() - 1] >= max_seq(prefix) { a[a.len() - 1] } else { max_seq(prefix) });
        }
    }
}

proof fn min_seq_in(a: Seq<int>)
    requires a.len() > 0,
    ensures exists|i: int| 0 <= i < a.len() && a[i] == min_seq(a),
    decreases a.len()
{
    if a.len() == 1 {
        assert(a[0] == min_seq(a));
    } else {
        let prefix = a.subrange(0, a.len() - 1);
        min_seq_in(prefix);
        if a[a.len() - 1] <= min_seq(prefix) {
            assert(min_seq(a) == a[a.len() - 1]);
        } else {
            assert(min_seq(a) == min_seq(prefix));
        }
    }
}

proof fn max_seq_in(a: Seq<int>)
    requires a.len() > 0,
    ensures exists|i: int| 0 <= i < a.len() && a[i] == max_seq(a),
    decreases a.len()
{
    if a.len() == 1 {
        assert(a[0] == max_seq(a));
    } else {
        let prefix = a.subrange(0, a.len() - 1);
        max_seq_in(prefix);
        if a[a.len() - 1] >= max_seq(prefix) {
            assert(max_seq(a) == a[a.len() - 1]);
        } else {
            assert(max_seq(a) == max_seq(prefix));
        }
    }
}

proof fn min_seq_push(a: Seq<int>, x: int)
    requires a.len() > 0,
    ensures
        min_seq(a.push(x)) == if x <= min_seq(a) { x } else { min_seq(a) }
{
    let extended = a.push(x);
    if a.len() == 1 {
        let prefix = a.subrange(0, a.len() - 1);
        assert(prefix.len() == 0);
        // Base case for recursion in min_seq
        if x <= a[0] {
            assert(min_seq(extended) == x);
        } else {
            assert(min_seq(extended) == a[0]);
        }
    } else {
        let prefix = a.subrange(0, a.len() - 1);
        min_seq_push(prefix, a[a.len() - 1]);
        if x <= min_seq(a) {
            assert(min_seq(extended) == x);
        } else {
            assert(min_seq(extended) == min_seq(a));
        }
    }
}

proof fn max_seq_push(a: Seq<int>, x: int)
    requires a.len() > 0,
    ensures
        max_seq(a.push(x)) == if x >= max_seq(a) { x } else { max_seq(a) }
{
    let extended = a.push(x);
    if a.len() == 1 {
        let prefix = a.subrange(0, a.len() - 1);
        assert(prefix.len() == 0);
        if x >= a[0] {
            assert(max_seq(extended) == x);
        } else {
            assert(max_seq(extended) == a[0]);
        }
    } else {
        let prefix = a.subrange(0, a.len() - 1);
        max_seq_push(prefix, a[a.len() - 1]);
        if x >= max_seq(a) {
            assert(max_seq(extended) == x);
        } else {
            assert(max_seq(extended) == max_seq(a));
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn sum_min_max(a: &[i32]) -> (sum: i32)
    requires a.len() > 0
    ensures sum == max_seq(a@.map(|i: int, x: i32| x as int)) + min_seq(a@.map(|i: int, x: i32| x as int))
// </vc-spec>
// <vc-code>
{
    let mut min_val = a[0];
    let mut max_val = a[0];
    let mut i: usize = 1;
    while i < a.len()
        invariant
            i <= a.len(),
            min_val as int == min_seq(a@.subrange(0, i).map(|j: int, x: i32| x as int)),
            max_val as int == max_seq(a@.subrange(0, i).map(|j: int, x: i32| x as int)),
        decreases a.len() - i
    {
        let current = a[i];
        let ghost seq_so_far = a@.subrange(0, i).map(|j: int, x: i32| x as int);
        let ghost extended_seq = a@.subrange(0, i + 1).map(|j: int, x: i32| x as int);
        
        proof {
            assert(extended_seq =~= seq_so_far.push(current as int));
            min_seq_push(seq_so_far, current as int);
            max_seq_push(seq_so_far, current as int);
        }
        
        if current < min_val {
            min_val = current;
        } else {
            proof {
                min_seq_nonempty(seq_so_far, i as int);
                assert(current as int >= min_seq(seq_so_far));
            }
        }
        
        if current > max_val {
            max_val = current;
        } else {
            proof {
                max_seq_nonempty(seq_so_far, i as int);
                assert(current as int <= max_seq(seq_so_far));
            }
        }
        i += 1;
    }
    min_val + max_val
}
// </vc-code>

fn main() {}

}