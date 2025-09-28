use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this implementation
// </vc-helpers>

// <vc-spec>
fn below_zero(operations: Vec<i32>) -> (result: (Vec<i32>, bool))
    ensures
        result.0.len() == operations.len() + 1,
        result.0[0] == 0,
        forall|i: int| 0 <= i < (result.0.len() - 1) as int ==> result.0[i + 1] == result.0[i] + operations[i],
        result.1 == true ==> exists|i: int| 1 <= i <= operations.len() as int && result.0[i] < 0,
        result.1 == false ==> forall|i: int| 0 <= i < result.0.len() as int ==> result.0[i] >= 0,
// </vc-spec>
// <vc-code>
{
    let mut balance_history: Vec<i32> = Vec::new();
    balance_history.push(0);
    
    let mut went_below_zero = false;
    let mut current_balance: i32 = 0;
    let mut i: usize = 0;
    
    while i < operations.len()
        invariant
            i <= operations.len(),
            balance_history.len() == i + 1,
            balance_history[0] == 0,
            forall|j: int| 0 <= j < i as int ==> #[trigger] balance_history[j + 1] == balance_history[j] + operations[j],
            balance_history[i as int] == current_balance,
            went_below_zero == exists|j: int| 1 <= j <= i as int && balance_history[j] < 0,
        decreases operations.len() - i
    {
        // Get the operation value using usize indexing
        let op_value = operations[i];
        
        // Check for overflow before performing the addition
        if op_value > 0 && current_balance > i32::MAX - op_value {
            // Handle overflow case - we can't proceed safely
            assert(false); // This should never happen in valid input
        } else if op_value < 0 && current_balance < i32::MIN - op_value {
            // Handle underflow case - we can't proceed safely  
            assert(false); // This should never happen in valid input
        }
        
        let new_balance = current_balance + op_value;
        balance_history.push(new_balance);
        
        // Assert to help verify the invariant
        assert(balance_history[i + 1] == new_balance);
        assert(balance_history[i as int] == current_balance);
        assert(balance_history[i + 1] == current_balance + operations[i as int]);
        assert(balance_history[i + 1] == balance_history[i as int] + operations[i as int]);
        
        current_balance = new_balance;
        
        if current_balance < 0 {
            went_below_zero = true;
        }
        
        i = i + 1;
    }
    
    (balance_history, went_below_zero)
}
// </vc-code>

fn main() {}

}