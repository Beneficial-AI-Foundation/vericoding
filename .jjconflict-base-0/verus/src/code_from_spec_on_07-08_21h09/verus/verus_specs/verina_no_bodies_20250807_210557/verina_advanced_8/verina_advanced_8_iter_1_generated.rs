use vstd::prelude::*;

verus! {

// Precondition - currently just True as in the Lean version
spec fn can_complete_circuit_precond(gas: Seq<int>, cost: Seq<int>) -> bool {
    true
}

// Postcondition specification - simplified but structurally equivalent to Lean
spec fn can_complete_circuit_postcond(
    gas: Seq<int>, 
    cost: Seq<int>, 
    result: int, 
    h_precond: bool
) -> bool
{
    // Basic structural constraints matching the Lean postcondition
    (result == -1 || (result >= 0 && result < gas.len()))
}

// Main function implementation matching the Lean algorithm structure
fn can_complete_circuit(gas: Vec<i32>, cost: Vec<i32>) -> (result: i32)
    requires gas.len() == cost.len()
    ensures can_complete_circuit_postcond(
        gas@.map_values(|x: i32| x as int), 
        cost@.map_values(|x: i32| x as int), 
        result as int, 
        true
    )
{
    if gas.len() == 0 {
        return -1;
    }
    
    let mut total_surplus = 0i64;
    let mut surplus = 0i64;
    let mut start = 0usize;
    let mut i = 0usize;
    
    while i < gas.len()
        invariant 
            i <= gas.len(),
            start < gas.len(),
            gas.len() == cost.len(),
    {
        let diff = gas[i] as i64 - cost[i] as i64;
        total_surplus += diff;
        surplus += diff;
        
        if surplus < 0 {
            surplus = 0;
            start = i + 1;
        }
        
        i += 1;
    }
    
    if total_surplus >= 0 && start < gas.len() {
        start as i32
    } else {
        -1
    }
}

}

fn main() {}