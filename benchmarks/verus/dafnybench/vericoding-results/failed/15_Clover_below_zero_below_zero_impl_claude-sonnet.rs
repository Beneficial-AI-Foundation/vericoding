use vstd::prelude::*;

verus! {

// <vc-helpers>

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
    let mut result = Vec::new();
    result.push(0);
    
    let mut current_balance: i32 = 0;
    let mut went_below_zero = false;
    
    for i in 0..operations.len()
        invariant
            result.len() == i + 1,
            result[0] == 0,
            current_balance == result[i as int],
            forall|j: int| 0 <= j < i as int ==> #[trigger] result[j + 1] == result[j] + operations[j],
            went_below_zero == exists|j: int| 1 <= j < result.len() as int && result[j] < 0,
            !went_below_zero ==> forall|j: int| 0 <= j < result.len() as int ==> result[j] >= 0,
    {
        match current_balance.checked_add(operations[i]) {
            Some(new_balance) => {
                current_balance = new_balance;
            },
            None => {
                current_balance = if operations[i] > 0 { i32::MAX } else { i32::MIN };
            }
        }
        result.push(current_balance);
        
        if current_balance < 0 {
            went_below_zero = true;
        }
        
        assert(result.len() == i + 2);
        assert(result[(i + 1) as int] == current_balance);
        assert(forall|j: int| 0 <= j < i as int ==> #[trigger] result[j + 1] == result[j] + operations[j]);
        assert(result[(i + 1) as int] == result[i as int] + operations[i as int]);
    }
    
    (result, went_below_zero)
}
// </vc-code>

fn main() {}

}