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
/* helper modified by LLM (iteration 5): Fixed syntax and simplified helpers */
proof fn sum_take_map_nonnegative_lemma(ops: Seq<i32>, i: int)
    requires
        0 <= i <= ops.len(),
        forall|j: int| 0 <= j <= ops.len() ==> sum(ops.take(j).map(|_idx, k: i32| k as int)) >= 0,
    ensures
        sum(ops.take(i).map(|_idx, k: i32| k as int)) >= 0,
{
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
/* code modified by LLM (iteration 5): Fixed compilation error with proper syntax */
{
    let mut balance: int = 0;
    let mut idx: usize = 0;
    
    while idx < operations.len()
        invariant
            balance == sum(operations@.take(idx).map(|_idx, j: i32| j as int)),
            forall|j: int| 0 <= j <= idx as int ==> sum(operations@.take(j).map(|_idx, k: i32| k as int)) >= 0
        decreases operations.len() - idx
    {
        let op = operations[idx];
        balance = balance + op as int;
        
        if balance < 0 {
            return true;
        }
        
        idx = idx + 1;
    }
    
    false
}
// </vc-code>

}
fn main() {}