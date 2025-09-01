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
// <vc-helpers>
proof fn sum_take_map_succ(s: Seq<i32>, k: int)
    requires
        0 <= k && k + 1 <= s.len(),
    ensures
        sum(s.take(k + 1).map(|_idx, v: i32| v as int))
            == sum(s.take(k).map(|_idx, v: i32| v as int)) + (s@[k] as int),
    decreases
        k,
{
    if k == 0 {
        // sum(take(1).map(...)) == mapped head
        // sum(take(0).map(...)) == 0
        assert(s.take(0).map(|_i, v: i32| v as int).len() == 0);
        assert(sum(s.take(0).map(|_i, v: i32| v as int)) == 0);

        // take(1).map(...) is a sequence of length 1 whose 0th element is s@[0] as int
        assert(s.take(1).map(|
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
// <vc-helpers>
proof fn sum_take_map_succ(s: Seq<i32>, k: int)
    requires
        0 <= k && k + 1 <= s.len(),
    ensures
        sum(s.take(k + 1).map(|_idx, v: i32| v as int))
            == sum(s.take(k).map(|_idx, v: i32| v as int)) + (s@[k] as int),
    decreases
        k,
{
    if k == 0 {
        // sum(take(1).map(...)) == mapped head
        // sum(take(0).map(...)) == 0
        assert(s.take(0).map(|_i, v: i32| v as int).len() == 0);
        assert(sum(s.take(0).map(|_i, v: i32| v as int)) == 0);

        // take(1).map(...) is a sequence of length 1 whose 0th element is s@[0] as int
        assert(s.take(1).map(|
// </vc-code>

fn main() {}
}