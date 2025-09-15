// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Fixed type mismatches by using int instead of usize for index parameter and proper type casting */
spec fn cumulative_sum(operations: &Vec<i32>, index: int) -> i32
    requires 0 <= index <= operations.len()
    decreases index
{
    if index == 0 {
        0
    } else {
        cumulative_sum(operations, index - 1) + operations[(index - 1) as usize]
    }
}

proof fn cumulative_sum_lemma(operations: &Vec<i32>, i: int)
    requires 0 <= i < operations.len()
    ensures cumulative_sum(operations, i + 1) == cumulative_sum(operations, i) + operations[i as usize]
{
}
// </vc-helpers>

// <vc-spec>
fn below_zero(operations: &Vec<i32>) -> (result: (Vec<i32>, bool))
    ensures
        result.0.len() == operations.len() + 1,
        result.0[0] == 0,
        forall|i: int| 0 <= i < operations.len() ==> result.0[i + 1] == result.0[i] + operations[i],
        result.1 == (exists|i: int| 1 <= i < result.0.len() && result.0[i] < 0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Fixed type mismatches by casting int to usize for indexing operations */
    let mut balances = Vec::new();
    balances.push(0);
    let mut has_negative = false;
    
    for i in 0..operations.len()
        invariant
            balances.len() == i + 1,
            balances[0] == 0,
            forall|j: int| 0 <= j < i ==> balances[j + 1] == balances[j] + operations[j as usize],
            has_negative == (exists|k: int| 1 <= k < balances.len() && balances[k] < 0),
    {
        let new_balance = balances[i] + operations[i];
        balances.push(new_balance);
        
        if new_balance < 0 {
            has_negative = true;
        }
        
        proof {
            assert(balances[i + 1] == balances[i] + operations[i]);
        }
    }
    
    (balances, has_negative)
}
// </vc-code>

}
fn main() {}