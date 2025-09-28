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
    /* code modified by LLM (iteration 5): fixed invariant logic and proof for negative balance detection */
    let mut balances = Vec::new();
    balances.push(0);
    
    let mut current_balance: i32 = 0;
    let mut found_negative = false;
    
    let mut i = 0;
    while i < operations.len()
        invariant
            balances.len() == i + 1,
            balances[0] == 0,
            current_balance == balances[i as int],
            forall|j: int| 0 <= j < i ==> balances[j + 1] == balances[j] + operations[j],
            found_negative == (exists|j: int| 1 <= j < balances.len() && balances[j] < 0),
        decreases operations.len() - i
    {
        let op = operations[i];
        let new_balance = if op > 0 && current_balance > i32::MAX - op {
            i32::MAX
        } else if op < 0 && current_balance < i32::MIN - op {
            i32::MIN
        } else {
            current_balance + op
        };
        
        current_balance = new_balance;
        balances.push(current_balance);
        
        if current_balance < 0 {
            found_negative = true;
        }
        
        proof {
            if current_balance < 0 {
                assert(balances[balances.len() - 1] < 0);
                assert(1 <= (balances.len() - 1) < balances.len());
                assert(exists|j: int| 1 <= j < balances.len() && balances[j] < 0);
            }
        }
        
        i = i + 1;
    }
    
    (balances, found_negative)
}
// </vc-code>

}
fn main() {}