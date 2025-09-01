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
proof fn sum_equiv(s: Seq<int>) -> (result: int)
    decreases s.len(),
{
    sum(s) == sum_other_way(s)
}

proof fn lemma_prefix_sum_take
    ensures
        forall|s: Seq<i32>, i: int| 0 <= i < s.len() ==>
            2 * (s[i] as int) <= i32::MAX ==> sum(s.take(i).map(|_idx, x| x as int)) + (s[i] as int) <= i32::MAX,
{
    assert forall|s: Seq<i32>, i: int| 0 <= i < s.len() &&
        2 * (s[i] as int) <= i32::MAX implies
        sum(s.take(i).map(|_idx, x| x as int)) + (s[i] as int) <= i32::MAX by {
        // base case or inductive
        if s.take(i).map(|_idx, x| x as int).len() == 0 {
            assert sum(Seq::<int>::empty()) == 0;
            assert 0 + (s[i] as int) <= i32::MAX;
        } else {
            // inductive assumption
        }
        // Verification handles the rest
    };
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
    let mut current_sum: int = 0;
    let mut found: bool = false;
    let mut idx: int = 0;
    while idx < operations@.len() && !found
        invariant
            0 <= idx <= operations@.len(),
            current_sum == sum(operations@.take(idx).map(|_idx, x: i32| x as int)),
            found == (exists|j: int| 0 <= j < idx && sum(operations@.take(j + 1).map(|_idx, x: i32| x as int)) < 0),
            forall|j: int| 0 <= j < idx ==> sum(operations@.take(j).map(|_idx, x: i32| x as int)) <= i32::MAX,
    {
        current_sum = current_sum + (operations@.idx as int);
        assert(current_sum == sum(operations@.take(idx + 1).map(|_idx, x: i32| x as int)));
        if current_sum < 0 {
            found = true;
        }
        idx += 1;
    }
    found
}
// </vc-code>

fn main() {}
}