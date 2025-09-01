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
proof fn sum_equiv(s: Seq<int>)
    decreases s.len()
    ensures sum(s) == sum_other_way(s)
{
    if s.len() == 0 {
    } else {
        sum_equiv(s.skip(1));
        assert(sum(s.take(s.len() - 1)) + s[s.len() - 1] == sum(s));
        assert(sum(s.take(s.len() - 1)) == sum_other_way(s.take(s.len() - 1))) by {
            sum_equiv(s.take(s.len() - 1));
        };
        assert(sum_other_way(s) == sum(s.take(s.len() - 1)) + s[s.len() - 1]);
    }
}

proof fn lemma_prefix_sum_take()
    ensures
        forall|s: Seq<i32>, i: int|
            0 <= i < s.len() ==> 2 * (s[i] as int) <= i32::MAX ==>
                sum(s.take(i).map(|_idx, x| x as int)) + (s[i] as int) <= i32::MAX
{
    assert forall|s: Seq<i32>, i: int| 0 <= i < s.len() &&
        2 * (s[i] as int) <= i32::MAX implies
        sum(s.take(i).map(|_idx, x| x as int)) + (s[i] as int) <= i32::MAX by {
        lemma_prefix_sum_take_aux(s, i);
    };
}

proof fn lemma_prefix_sum_take_aux(s: Seq<i32>, i: int)
    decreases s.len()
    requires 0 <= i < s.len()
    requires 2 * (s[i] as int) <= i32::MAX
    ensures sum(s.take(i).map(|_idx, x| x as int)) + (s[i] as int) <= i32::MAX
{
    if i == 0 {
        assert(sum(Seq::<int>::empty()) + (s[0] as int) == (s[0] as int));
        assert((s[0] as int) <= i32::MAX);
    } else {
        lemma_prefix_sum_take_aux(s, i - 1);
        assert(2 * (s[i - 1] as int) <= i32::MAX);
        assert(sum(s.take(i).map(|_idx, x| x as int)) == sum(s.take(i - 1).map(|_idx, x| x as int)) + (s[i
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
proof fn sum_equiv(s: Seq<int>)
    decreases s.len()
    ensures sum(s) == sum_other_way(s)
{
    if s.len() == 0 {
    } else {
        sum_equiv(s.skip(1));
        assert(sum(s.take(s.len() - 1)) + s[s.len() - 1] == sum(s));
        assert(sum(s.take(s.len() - 1)) == sum_other_way(s.take(s.len() - 1))) by {
            sum_equiv(s.take(s.len() - 1));
        };
        assert(sum_other_way(s) == sum(s.take(s.len() - 1)) + s[s.len() - 1]);
    }
}

proof fn lemma_prefix_sum_take()
    ensures
        forall|s: Seq<i32>, i: int|
            0 <= i < s.len() ==> 2 * (s[i] as int) <= i32::MAX ==>
                sum(s.take(i).map(|_idx, x| x as int)) + (s[i] as int) <= i32::MAX
{
    assert forall|s: Seq<i32>, i: int| 0 <= i < s.len() &&
        2 * (s[i] as int) <= i32::MAX implies
        sum(s.take(i).map(|_idx, x| x as int)) + (s[i] as int) <= i32::MAX by {
        lemma_prefix_sum_take_aux(s, i);
    };
}

proof fn lemma_prefix_sum_take_aux(s: Seq<i32>, i: int)
    decreases s.len()
    requires 0 <= i < s.len()
    requires 2 * (s[i] as int) <= i32::MAX
    ensures sum(s.take(i).map(|_idx, x| x as int)) + (s[i] as int) <= i32::MAX
{
    if i == 0 {
        assert(sum(Seq::<int>::empty()) + (s[0] as int) == (s[0] as int));
        assert((s[0] as int) <= i32::MAX);
    } else {
        lemma_prefix_sum_take_aux(s, i - 1);
        assert(2 * (s[i - 1] as int) <= i32::MAX);
        assert(sum(s.take(i).map(|_idx, x| x as int)) == sum(s.take(i - 1).map(|_idx, x| x as int)) + (s[i
// </vc-code>

fn main() {}
}