use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
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
    
    // Sort candidates by their values in descending order (bubble sort for simplicity)
    if Valores[candidates[0]] < Valores[candidates[1]] {
        let temp = candidates[0];
        candidates[0] = candidates[1];
        candidates[1] = temp;
    }
    
    if Valores[candidates[1]] < Valores[candidates[2]] {
        let temp = candidates[1];
        candidates[1] = candidates[2];
        candidates[2] = temp;
    }
    
    if Valores[candidates[0]] < Valores[candidates[1]] {
        let temp = candidates[0];
        candidates[0] = candidates[1];
        candidates[1] = temp;
    }
    
    // Return the two best candidates as parents
    (candidates[0], candidates[1])
}

}