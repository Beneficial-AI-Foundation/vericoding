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
    decreases s.len(),
    ensures sum(s) == sum_other_way(s)
{
    if s.len() == 0 {
    } else {
        sum_equiv(s.skip(1));
        assert(sum(s.take(s.len() - 1)) + s[s.len() - 1] == sum(s));
        assert(sum(s.take(s.len() - 1)) == sum_other_way(s.take(s.len - 1))) by {
            sum_equiv(s.take(s.len() - 1));
        };
        assert(sum_other_way(s) == sum(s.take(s.len() - 1)) + s[s.len() - 1]);
    }
}

proof fn lemma_prefix_sum_take()
    ensures
        forall|s
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
    decreases s.len(),
    ensures sum(s) == sum_other_way(s)
{
    if s.len() == 0 {
    } else {
        sum_equiv(s.skip(1));
        assert(sum(s.take(s.len() - 1)) + s[s.len() - 1] == sum(s));
        assert(sum(s.take(s.len() - 1)) == sum_other_way(s.take(s.len - 1))) by {
            sum_equiv(s.take(s.len() - 1));
        };
        assert(sum_other_way(s) == sum(s.take(s.len() - 1)) + s[s.len() - 1]);
    }
}

proof fn lemma_prefix_sum_take()
    ensures
        forall|s
// </vc-code>

fn main() {}
}