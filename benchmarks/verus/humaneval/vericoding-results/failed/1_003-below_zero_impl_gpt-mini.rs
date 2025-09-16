// <vc-preamble>
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

spec fn sum_other_way(s: Seq<int>) -> (result:int)
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        s[s.len() - 1] + sum_other_way(s.take(s.len() - 1))
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemma relating sum of take(k+1) to sum(take(k)) + ops@[k] */
proof fn sum_take_succ(ops: Vec<i32>, k: int)
    requires
        0 <= k && k < ops@.len(),
    ensures
        sum(ops@.take(k+1).map(|_idx, j: i32| j as int)) == sum(ops@.take(k).map(|_idx, j: i32| j as int)) + (ops@[k] as int),
    decreases
        k
{
    if k == 0 {
        assert(sum(ops@.take(0).map(|_idx, j: i32| j as int)) == 0);
        assert(sum(ops@.take(1).map(|_idx, j: i32| j as int)) == (ops@[0] as int) + sum(ops@.take(0).map(|_idx, j: i32| j as int)));
    } else {
        sum_take_succ(ops, k - 1);
        assert(sum(ops@.take(k+1).map(|_idx, j: i32| j as int)) == sum(ops@.take(k).map(|_idx, j: i32| j as int)) + (ops@[k] as int));
    }
}
// </vc-helpers>

// <vc-spec>
fn below_zero(operations: Vec<i32>) -> (result: bool)

    requires
        forall|i: int|
            0 <= i <= operations@.len() ==> sum(operations@.take(i).map(|_idx, j: i32| j as int))
                <= i32::MAX,

    ensures
        result <==> exists|i: int|
            0 <= i <= operations@.len() && sum(operations@.take(i).map(|_idx, j: i32| j as int))
                < 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate runtime Vec and maintain invariant linking acc_rt and prefix sums, using helper lemma */
    let mut idx: usize = 0;
    let mut acc_rt: i32 = 0;
    while idx < operations.len()
        invariant
            0 <= (idx as int),
            (idx as int) <= operations@.len(),
            (acc_rt as int) == sum(operations@.take(idx as int).map(|_idx, j: i32| j as int)),
            forall|j: int| 0 <= j <= (idx as int) ==> sum(operations@.take(j).map(|_idx, j: i32| j as int)) >= 0,
        decreases
            operations@.len() - (idx as nat)
    {
        let x: i32 = operations[idx];
        acc_rt = acc_rt + x;
        if acc_rt < 0 {
            proof {
                let witness: int = (idx as int) + 1;
                sum_take_succ(operations, idx as int);
                assert(sum(operations@.take(witness).map(|_idx, j: i32| j as int)) == (acc_rt as int));
                assert((acc_rt as int) < 0);
                assert(exists|i: int| 0 <= i <= operations@.len() && sum(operations@.take(i).map(|_idx, j: i32| j as int)) < 0);
            }
            return true;
        }
        proof {
            sum_take_succ(operations, idx as int);
            assert((acc_rt as int) == sum(operations@.take((idx as int) + 1).map(|_idx, j: i32| j as int)));
            assert((acc_rt as int) >= 0);
            assert(forall|j: int| 0 <= j <= (idx as int) + 1 ==> sum(operations@.take(j).map(|_idx, j: i32| j as int)) >= 0);
        }
        idx = idx + 1;
    }
    proof {
        assert(!exists|i: int| 0 <= i <= operations@.len() && sum(operations@.take(i).map(|_idx, j: i32| j as int)) < 0);
    }
    return false;
}
// </vc-code>

}
fn main() {}