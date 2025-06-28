use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Helper spec function to check if a value is one of the three candidates
spec fn is_candidate(val: usize, i: usize, j: usize, k: usize) -> bool {
    val == i || val == j || val == k
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
    
    // Prove that all candidates are valid indices
    assert(candidates[0] < Valores.len());
    assert(candidates[1] < Valores.len());  
    assert(candidates[2] < Valores.len());
    
    // Sort candidates by their values in descending order (bubble sort for simplicity)
    if Valores[candidates[0]] < Valores[candidates[1]] {
        let temp = candidates[0];
        candidates[0] = candidates[1];
        candidates[1] = temp;
    }
    
    // Maintain invariant that all elements are still candidates
    assert(is_candidate(candidates[0], i, j, k));
    assert(is_candidate(candidates[1], i, j, k));
    assert(is_candidate(candidates[2], i, j, k));
    assert(candidates[0] < Valores.len());
    assert(candidates[1] < Valores.len());
    assert(candidates[2] < Valores.len());
    
    if Valores[candidates[1]] < Valores[candidates[2]] {
        let temp = candidates[1];
        candidates[1] = candidates[2];
        candidates[2] = temp;
    }
    
    // Maintain invariant
    assert(is_candidate(candidates[0], i, j, k));
    assert(is_candidate(candidates[1], i, j, k));
    assert(is_candidate(candidates[2], i, j, k));
    assert(candidates[0] < Valores.len());
    assert(candidates[1] < Valores.len());
    assert(candidates[2] < Valores.len());
    
    if Valores[candidates[0]] < Valores[candidates[1]] {
        let temp = candidates[0];
        candidates[0] = candidates[1];
        candidates[1] = temp;
    }
    
    // Final assertions to help prove postconditions
    assert(is_candidate(candidates[0], i, j, k));
    assert(is_candidate(candidates[1], i, j, k));
    assert(candidates[0] < Valores.len());
    assert(candidates[1] < Valores.len());
    
    // Prove that the two selected parents are different
    // Since we started with three distinct values {i, j, k} and only rearranged them,
    // candidates[0] and candidates[1] must be different
    assert(candidates[0] != candidates[1]) by {
        // The array still contains the three distinct values i, j, k
        // candidates[0] and candidates[1] are two of these three values
        // Since i != j && j != k && k != i, any two different positions
        // in the candidates array must contain different values
    };
    
    // Return the two best candidates as parents
    (candidates[0], candidates[1])
}

}