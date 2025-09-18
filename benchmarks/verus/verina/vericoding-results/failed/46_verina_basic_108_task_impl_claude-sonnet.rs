// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed sequence indexing to use int instead of usize */
fn compute_balance_and_check(operations: &Vec<i32>) -> (result: (Vec<i32>, bool))
    requires
        operations.len() < usize::MAX,
    ensures
        result.0.len() == operations.len() + 1,
        result.0@[0] == 0,
        forall|i: int| 0 <= i < operations.len() ==> result.0@[i + 1] == result.0@[i] + operations@[i],
        result.1 == (exists|i: int| 1 <= i < result.0.len() && result.0@[i] < 0),
{
    let mut balance = Vec::new();
    balance.push(0);
    let mut below_zero_found = false;
    
    for i in 0..operations.len()
        invariant
            balance.len() == i + 1,
            balance@[0] == 0,
            forall|j: int| 0 <= j < i ==> balance@[j + 1] == balance@[j] + operations@[j],
            below_zero_found == (exists|j: int| 1 <= j < balance.len() && balance@[j] < 0),
    {
        proof {
            assert(i < operations.len());
            assert(balance.len() == i + 1);
            assert(i < balance.len());
        }
        let new_balance = balance[i as usize] + operations[i as usize];
        balance.push(new_balance);
        if new_balance < 0 {
            below_zero_found = true;
        }
        proof {
            assert(balance.len() == i + 2);
            assert(balance@[i as int + 1] == balance@[i as int] + operations@[i as int]);
        }
    }
    
    (balance, below_zero_found)
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
    /* code modified by LLM (iteration 5): simplified to call helper directly */
    if operations.len() >= usize::MAX {
        let mut balance = Vec::new();
        balance.push(0);
        return (balance, false);
    }
    compute_balance_and_check(operations)
}
// </vc-code>

}
fn main() {}