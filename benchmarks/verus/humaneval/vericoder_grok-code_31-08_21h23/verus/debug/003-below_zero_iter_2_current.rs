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
    ensures sum(s) == sum_other_way(s),
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
                sum(s.take(i).map(|_idx, x| x as int)) + (s[i] as int) <= i32::MAX,
{
    assert forall|s: Seq<i32>, i: int| 0 <= i < s.len() &&
        2 * (s[i] as int) <= i32::MAX implies
        !sum(s.take(i).map(|_idx, x| x as int)) + (s[i] as int) <= i32::MAX by {
        lemma_prefix_sum_take_aux(s, i);
    };
}

proof fn lemma_prefix_sum_take_aux(s: Seq<i32>, i: int)
    decreases s.len(),
    requires 0 <= i < s.len(),
    requires 2 * (s[i] as int) <= i32::MAX,
    ensures sum(s.take(i).map(|_idx, x| x as int)) + (s[i] as int) <= i32::MAX,
{
    if i == 0 {
        assert(sum(Seq::<int>::empty()) + (s[0] as int) == (s[0] as int));
        assert((s[0] as int) <= 2 * (s[0] as int)); // since 2 * x / 2 <= max, but since 2*x <= max, ok for positive, but s[i] can be negative? Assuming i32, but the condition is 2*s[i] <= i32::MAX, which implies s[i] <= i32::MAX/2, and since sum take(0)=0 <= max, 0 + s[i] <= max anyway if s[i] <= 2*s[i], but to be precise, since pre requires it, it holds.
    } else {
        assert(i32::MAX / 2 >= s[i] as int);
        assert(s.take(i)[i-1] == s[i-1]);
        assert(sum(s.take(i).map(|_idx, x| x as int)) == sum(s.take(i-1).map(|_idx, x| x as int)) + (s[i-1] as int));
        assert(2 * (s[i-1] as int) <= 2 * (i32::MAX as int / 2)) by {
            if s[i-1] as int < 0 {
            } else {
            }
        };
    }
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
    let mut idx: nat = 0;
    let ghost operations_seq: Seq<i32> = operations@;
    while idx < operations_seq.len() && !found
        invariant
            0 <= idx <= operations_seq.len(),
            current_sum == sum(operations_seq.take(idx).map(|_idx, x: i32| x as int)),
            found == (exists|j: nat| 0 <= j < idx && sum(operations_seq.take(j + 1).map(|_idx, x: i32| x as int)) < 0),
            forall|j: nat| 0 <= j <= idx ==> sum(operations_seq.take(j).map(|_idx, x: i32| x as int)) <= i32::MAX,
    {
        current_sum = current_sum + (operations_seq[idx] as int);
        assert(current_sum == sum(operations_seq.take(idx + 1).map(|_idx, x: i32| x as int)));
        if current_sum < 0 {
            found = true;
        }
        idx += 1;
        // Ensure max sum for new idx
        assert(sum(operations_seq.take(idx).map(|_idx, x: i32| x as int)) <= i32::MAX);
    }
    if idx == operations_seq.len() && current_sum < 0 {
        found = true;
    }
    found
}
// </vc-code>

fn main() {}
}