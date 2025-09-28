// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No helper functions needed */
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
/* code modified by LLM (iteration 5): Fix compilation error related to operations indexing by casting j to usize */
{
    let mut current_balance: i32 = 0;
    let mut balances: Vec<i32> = Vec::new();
    let mut below_zero_found: bool = false;

    balances.push(current_balance);

    let mut i = 0;
    while i < operations.len()
        invariant
            0 <= i as int <= operations.len() as int,
            balances.len() == i + 1,
            balances[0] == 0,
            (forall|j: int| 0 <= j < i as int ==> balances[j+1] == balances[j] + operations[j as usize]),
            below_zero_found == (exists |j: int| 1 <= j < balances.len() as int && balances[j] < 0),
            current_balance == balances[i as int],
        decreases operations.len() - i
    {
        current_balance = current_balance + operations[i];
        balances.push(current_balance);
        if current_balance < 0 {
            below_zero_found = true;
        }
        i = i + 1;
    }

    (balances, below_zero_found)
}
// </vc-code>

}
fn main() {}