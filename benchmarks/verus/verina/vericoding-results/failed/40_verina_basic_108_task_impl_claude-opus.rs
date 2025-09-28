// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): Fixed ghost type usage - removed 'as int' conversions in executable code */
    let mut balance = Vec::new();
    balance.push(0i32);
    let mut went_negative = false;
    let mut i: usize = 0;
    
    while i < operations.len()
        invariant
            i <= operations.len(),
            balance.len() == i + 1,
            balance[0] == 0,
            forall|j: int| 0 <= j < i ==> balance[j + 1] == balance[j] + operations[j],
            went_negative == (exists|j: int| 1 <= j <= i && balance[j] < 0),
        decreases operations.len() - i
    {
        let prev_balance = balance[i];
        let op = operations[i];
        let current_balance: i32 = prev_balance + op;
        balance.push(current_balance);
        
        if current_balance < 0 {
            went_negative = true;
        }
        
        assert(balance.len() == i + 2);
        assert(balance[(i + 1) as int] == balance[i as int] + operations[i as int]);
        
        i = i + 1;
    }
    
    (balance, went_negative)
}
// </vc-code>

}
fn main() {}