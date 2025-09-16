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
/* helper modified by LLM (iteration 3): added assert to guide recursive proof */
proof fn sum_snoc(s: Seq<int>, x: int)
    ensures
        sum(s.push(x)) == sum(s) + x,
    decreases s.len()
{
    if s.len() > 0 {
        assert(s.push(x).skip(1) == s.skip(1).push(x));
        sum_snoc(s.skip(1), x);
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
/* code modified by LLM (iteration 3): fixed invariants and added proof for early return */
{
    let mut current_sum: i64 = 0;
    let mut i: usize = 0;
    while i < operations.len()
        invariant
            0 <= i <= operations.len(),
            current_sum >= 0,
            current_sum as int == sum(operations@.take(i as int).map(|_idx, j: i32| j as int)),
            forall|k: int| 0 <= k <= i ==> sum(operations@.take(k).map(|_idx, j: i32| j as int)) >= 0,
        decreases operations.len() - i
    {
        let op = operations[i];
        
        proof {
            let ops_int = operations@.map(|_idx, j: i32| j as int);
            sum_snoc(ops_int.take(i as int), ops_int[i as int]);
        }

        current_sum = current_sum + (op as i64);

        if current_sum < 0 {
            proof {
                let ops_int = operations@.map(|_idx, j: i32| j as int);
                let k = (i + 1) as int;
                assert(current_sum as int == sum(ops_int.take(k)));
                assert(exists|j: int|
                    0 <= j <= operations@.len() && sum(operations@.take(j).map(|_idx, j: i32| j as int)) < 0
                );
            }
            return true;
        }
        i = i + 1;
    }
    return false;
}
// </vc-code>

}
fn main() {}