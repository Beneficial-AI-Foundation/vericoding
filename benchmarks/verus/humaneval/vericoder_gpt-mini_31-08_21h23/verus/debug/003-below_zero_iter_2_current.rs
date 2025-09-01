use vstd::prelude::*;

verus! {

spec fn sum(s: Seq<int>) -> (result:int)
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        s[0] + sum(s.skip(1))
    }
}
// pure-end
// pure-end

spec fn sum_other_way(s: Seq<int>) -> (result:int)
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        s[s.len() - 1] + sum_other_way(s.take(s.len() - 1))
    }
}
// pure-end

// <vc-helpers>
spec fn prefix_sum(operations: Vec<i32>, k: int) -> int
    requires 0 <= k && k <= operations@.len(),
    decreases k
{
    sum(operations@.take(k).map(|_idx, v: i32| v as int))
}
// </vc-helpers>

// <vc-spec>
fn below_zero(operations: Vec<i32>) -> (result: bool)
    // pre-conditions-start
    requires
        forall|i: int|
            0 <= i <= operations@.len() ==> sum(operations@.take(i).map(|_idx, j: i32| j as int))
                <= i32::MAX,
    // pre-conditions-end
    // post-conditions-start
    ensures
        result <==> exists|i: int|
            0 <= i <= operations@.len() && sum(operations@.take(i).map(|_idx, j: i32| j as int))
                < 0,
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let n: nat = operations@.len();
    let mut i: nat = 0;
    let mut curr: int = 0;
    while i < n
        invariant 0 <= i && i <= n
        invariant curr == prefix_sum(operations, i as int)
        invariant forall|j: int| 0 <= j && j <= i as int ==>
            prefix_sum(operations, j) >= 0
    {
        let x: i32 = operations@[i];
        let new_sum: int = curr + (x as int);
        // show that new_sum == prefix_sum(... take(i+1))
        if new_sum < 0 {
            proof {
                let k: int = (i as int) + 1;
                // k is between 0 and n
                assert(0 <= k && k <= n as int);
                // curr == prefix_sum(take(i))
                assert(curr == prefix_sum(operations, i as int));
                // new_sum == prefix_sum(take(k))
                assert(new_sum == prefix_sum(operations, k));
                // new_sum < 0
                assert(prefix_sum(operations, k) < 0);
                // hence witness exists
                assert(exists|j: int|
                    0 <= j && j <= n as int &&
                    prefix_sum(operations, j) < 0);
            }
            return true;
        }
        // otherwise update and continue
        curr = new_sum;
        i = i + 1;
    }
    // finished loop: no prefix sum < 0
    proof {
        // i == n here
        assert(i == n);
        // from invariant: for all j <= n, prefix_sum(...) >= 0
        assert(forall|j: int| 0 <= j && j <= n as int ==>
            prefix_sum(operations, j) >= 0);
        // so no witness exists
        assert(! (exists|j: int|
            0 <= j && j <= n as int &&
            prefix_sum(operations, j) < 0));
    }
    false
    // impl-end
}
// </vc-code>

fn main() {}
}