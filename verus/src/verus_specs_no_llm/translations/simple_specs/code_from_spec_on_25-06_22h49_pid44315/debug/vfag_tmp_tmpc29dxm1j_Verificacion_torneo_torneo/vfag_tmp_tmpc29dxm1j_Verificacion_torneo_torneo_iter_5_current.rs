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
    
    // Add proof that indices are valid
    proof {
        assert(i < Valores.len());
        assert(j < Valores.len());
        assert(k < Valores.len());
    }
    
    // First, find the candidate with the maximum value
    let max_pos = if Valores[i] >= Valores[j] && Valores[i] >= Valores[k] {
        proof {
            assert(i < Valores.len());
        }
        i
    } else if Valores[j] >= Valores[i] && Valores[j] >= Valores[k] {
        proof {
            assert(j < Valores.len());
        }
        j
    } else {
        proof {
            assert(k < Valores.len());
        }
        k
    };
    
    // Then find the second maximum from the remaining two candidates
    let second_max_pos = if max_pos == i {
        // Choose between j and k
        if Valores[j] >= Valores[k] {
            proof {
                assert(j < Valores.len());
            }
            j
        } else {
            proof {
                assert(k < Valores.len());
            }
            k
        }
    } else if max_pos == j {
        // Choose between i and k
        if Valores[i] >= Valores[k] {
            proof {
                assert(i < Valores.len());
            }
            i
        } else {
            proof {
                assert(k < Valores.len());
            }
            k
        }
    } else {
        // max_pos == k, choose between i and j
        if Valores[i] >= Valores[j] {
            proof {
                assert(i < Valores.len());
            }
            i
        } else {
            proof {
                assert(j < Valores.len());
            }
            j
        }
    };
    
    // Prove that our selections are valid
    proof {
        assert(max_pos == i || max_pos == j || max_pos == k);
        assert(second_max_pos == i || second_max_pos == j || second_max_pos == k);
        assert(max_pos < Valores.len());
        assert(second_max_pos < Valores.len());
        
        // Prove that max_pos != second_max_pos by case analysis
        if max_pos == i {
            assert(second_max_pos == j || second_max_pos == k);
            assert(i != j && i != k); // from precondition
            assert(max_pos != second_max_pos);
        } else if max_pos == j {
            assert(second_max_pos == i || second_max_pos == k);
            assert(j != i && j != k); // from precondition
            assert(max_pos != second_max_pos);
        } else {
            assert(max_pos == k);
            assert(second_max_pos == i || second_max_pos == j);
            assert(k != i && k != j); // from precondition
            assert(max_pos != second_max_pos);
        }
    }
    
    // Return the two best candidates as parents
    (max_pos, second_max_pos)
}

}