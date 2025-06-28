use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Helper spec function to check if a value is one of the three candidates
spec fn is_candidate(val: usize, i: usize, j: usize, k: usize) -> bool {
    val == i || val == j || val == k
}

// Helper spec function to check if an array contains all three distinct values
spec fn contains_all_three(arr: [usize; 3], i: usize, j: usize, k: usize) -> bool {
    (arr[0] == i || arr[0] == j || arr[0] == k) &&
    (arr[1] == i || arr[1] == j || arr[1] == k) &&
    (arr[2] == i || arr[2] == j || arr[2] == k) &&
    (arr[0] != arr[1] && arr[1] != arr[2] && arr[0] != arr[2])
}

fn torneo(Valores: &[f64], i: usize, j: usize, k: usize) -> (pos_padre: usize, pos_madre: usize)
    requires
        Valores.len() >= 20 && Valores.len() < 50,
        i < Valores.len() && j < Valores.len() && k < Valores.len(),
        i != j && j != k && k != i
    ensures
        pos_padre < Valores.len() && pos_madre < Valores.len(),
        pos_padre != pos_madre,
        (pos_padre == i || pos_padre == j || pos_padre == k),
        (pos_madre == i || pos_madre == j || pos_madre == k)
{
    // Tournament selection: select the two best (highest values) from the three candidates
    let mut candidates = [i, j, k];
    
    // Prove that all candidates are valid indices and distinct
    assert(candidates[0] < Valores.len());
    assert(candidates[1] < Valores.len());  
    assert(candidates[2] < Valores.len());
    assert(candidates[0] != candidates[1]);
    assert(candidates[1] != candidates[2]);
    assert(candidates[0] != candidates[2]);
    
    // Sort candidates by their values in descending order (bubble sort for simplicity)
    if Valores[candidates[0]] < Valores[candidates[1]] {
        let temp = candidates[0];
        candidates[0] = candidates[1];
        candidates[1] = temp;
    }
    
    // Maintain invariants
    assert(is_candidate(candidates[0], i, j, k));
    assert(is_candidate(candidates[1], i, j, k));
    assert(is_candidate(candidates[2], i, j, k));
    assert(candidates[0] < Valores.len());
    assert(candidates[1] < Valores.len());
    assert(candidates[2] < Valores.len());
    assert(candidates[0] != candidates[1]);
    assert(candidates[1] != candidates[2]);
    assert(candidates[0] != candidates[2]);
    
    if Valores[candidates[1]] < Valores[candidates[2]] {
        let temp = candidates[1];
        candidates[1] = candidates[2];
        candidates[2] = temp;
    }
    
    // Maintain invariants
    assert(is_candidate(candidates[0], i, j, k));
    assert(is_candidate(candidates[1], i, j, k));
    assert(is_candidate(candidates[2], i, j, k));
    assert(candidates[0] < Valores.len());
    assert(candidates[1] < Valores.len());
    assert(candidates[2] < Valores.len());
    assert(candidates[0] != candidates[1]);
    assert(candidates[1] != candidates[2]);
    assert(candidates[0] != candidates[2]);
    
    if Valores[candidates[0]] < Valores[candidates[1]] {
        let temp = candidates[0];
        candidates[0] = candidates[1];
        candidates[1] = temp;
    }
    
    // Final assertions to prove postconditions
    assert(is_candidate(candidates[0], i, j, k));
    assert(is_candidate(candidates[1], i, j, k));
    assert(candidates[0] < Valores.len());
    assert(candidates[1] < Valores.len());
    assert(candidates[0] != candidates[1]);
    
    // Return the two best candidates as parents
    (candidates[0], candidates[1])
}

}