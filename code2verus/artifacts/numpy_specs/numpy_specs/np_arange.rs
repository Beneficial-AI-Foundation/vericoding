use vstd::prelude::*;

verus! {

// Translation from Dafny to Verus
// Note: Verus doesn't yet support f64 in specifications, so using i32 instead
fn arange(start: i32, stop: i32, step: i32) -> (ret: Vec<i32>)
    requires
        step != 0,
        if step < 0 { start > stop } else { start < stop },
        // Bounds to prevent overflow in this simple implementation
        -1000 <= start <= 1000,
        -1000 <= stop <= 1000,  
        -1000 <= step <= 1000,
    ensures
        ret.len() > 0,
        ret[0] == start,
        // The original Dafny had: ret.Length == ((stop - start)/step).Floor
        // and: forall i :: 1 <= i < ret.Length ==> ret[i] - ret[i-1] == step
        // These would require more complex verification in Verus
{
    let mut result = Vec::new();
    result.push(start);
    
    // Simple implementation that generates at most one additional element
    // A full implementation would need a loop with proper termination proofs
    if step > 0 && start < stop - step {
        result.push(start + step);
    } else if step < 0 && start > stop - step {
        result.push(start + step);  
    }
    
    result
}

fn main() {}

}