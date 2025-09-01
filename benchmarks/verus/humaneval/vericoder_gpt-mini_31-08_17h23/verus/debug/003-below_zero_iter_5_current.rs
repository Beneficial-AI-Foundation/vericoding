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
// No helper lemmas required for this proof.
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
    let mut i: usize = 0usize;
    let mut running: int = 0;
    let mut found: bool = false;
    while i < operations.len() {
        invariant i <= operations.len();
        invariant running == sum(operations@.take(i as int).map(|_idx, j: i32| j as int));
        invariant found == exists|k: int|
            0 <= k && k <= (i as int) &&
            sum(operations@.take(k).map(|_idx, j: i32| j as int)) < 0;
        decreases operations.len() - i;
        {
            let new_i = i + 1;
            running = sum(operations@.take((new_i as int)).map(|_idx, j: i32| j as int));
            i = new_i;
            found = exists|k: int|
                0 <= k && k <= (i as int) &&
                sum(operations@.take(k).map(|_idx, j: i32| j as int)) < 0;
        }
    }
    found
    // impl-end
}
// </vc-code>

fn main() {}
}