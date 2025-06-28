use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn CanyonSearch(a: Vec<int>, b: Vec<int>) -> (d: nat)
    requires
        a.len() != 0 && b.len() != 0,
        forall|i: int, j: int| 0 <= i < j < a.len() ==> a.spec_index(i) <= a.spec_index(j),
        forall|i: int, j: int| 0 <= i < j < b.len() ==> b.spec_index(i) <= b.spec_index(j)
    ensures
        exists|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() && d == if a.spec_index(i) < b.spec_index(j) { (b.spec_index(j) - a.spec_index(i)) as nat } else { (a.spec_index(i) - b.spec_index(j)) as nat },
        forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() ==> d <= if a.spec_index(i) < b.spec_index(j) { (b.spec_index(j) - a.spec_index(i)) as nat } else { (a.spec_index(i) - b.spec_index(j)) as nat }
{
    let mut min_diff: nat = if a[0] < b[0] { (b[0] - a[0]) as nat } else { (a[0] - b[0]) as nat };
    let mut witness_i: usize = 0;
    let mut witness_j: usize = 0;
    
    // Use two-pointer technique for efficiency
    let mut i: usize = 0;
    let mut j: usize = 0;
    
    while i < a.len() && j < b.len()
        invariant
            i <= a.len(),
            j <= b.len(),
            witness_i < a.len(),
            witness_j < b.len(),
            min_diff == if a.spec_index(witness_i as int) < b.spec_index(witness_j as int) { 
                (b.spec_index(witness_j as int) - a.spec_index(witness_i as int)) as nat 
            } else { 
                (a.spec_index(witness_i as int) - b.spec_index(witness_j as int)) as nat 
            },
            // All pairs we've considered so far have diff >= min_diff
            forall|x: int, y: int| 0 <= x < i && 0 <= y <= j && y < b.len() ==> min_diff <= if a.spec_index(x) < b.spec_index(y) { 
                (b.spec_index(y) - a.spec_index(x)) as nat 
            } else { 
                (a.spec_index(x) - b.spec_index(y)) as nat 
            },
            forall|x: int, y: int| 0 <= x <= i && x < a.len() && 0 <= y < j ==> min_diff <= if a.spec_index(x) < b.spec_index(y) { 
                (b.spec_index(y) - a.spec_index(x)) as nat 
            } else { 
                (a.spec_index(x) - b.spec_index(y)) as nat 
            }
    {
        let curr_diff = if a[i] < b[j] { (b[j] - a[i]) as nat } else { (a[i] - b[j]) as nat };
        
        if curr_diff < min_diff {
            min_diff = curr_diff;
            witness_i = i;
            witness_j = j;
        }
        
        // Move the pointer with smaller value
        if a[i] <= b[j] {
            i = i + 1;
        } else {
            j = j + 1;
        }
    }
    
    // Handle remaining elements if one array is exhausted
    if i < a.len() {
        // Compare remaining elements of a with last element of b
        let last_b_idx = b.len() - 1;
        while i < a.len()
            invariant
                i <= a.len(),
                witness_i < a.len(),
                witness_j < b.len(),
                min_diff == if a.spec_index(witness_i as int) < b.spec_index(witness_j as int) { 
                    (b.spec_index(witness_j as int) - a.spec_index(witness_i as int)) as nat 
                } else { 
                    (a.spec_index(witness_i as int) - b.spec_index(witness_j as int)) as nat 
                },
                forall|x: int| 0 <= x < i ==> min_diff <= if a.spec_index(x) < b.spec_index(last_b_idx as int) { 
                    (b.spec_index(last_b_idx as int) - a.spec_index(x)) as nat 
                } else { 
                    (a.spec_index(x) - b.spec_index(last_b_idx as int)) as nat 
                }
        {
            let curr_diff = if a[i] < b[last_b_idx] { (b[last_b_idx] - a[i]) as nat } else { (a[i] - b[last_b_idx]) as nat };
            
            if curr_diff < min_diff {
                min_diff = curr_diff;
                witness_i = i;
                witness_j = last_b_idx;
            }
            
            i = i + 1;
        }
    }
    
    if j < b.len() {
        // Compare remaining elements of b with last element of a
        let last_a_idx = a.len() - 1;
        while j < b.len()
            invariant
                j <= b.len(),
                witness_i < a.len(),
                witness_j < b.len(),
                min_diff == if a.spec_index(witness_i as int) < b.spec_index(witness_j as int) { 
                    (b.spec_index(witness_j as int) - a.spec_index(witness_i as int)) as nat 
                } else { 
                    (a.spec_index(witness_i as int) - b.spec_index(witness_j as int)) as nat 
                },
                forall|y: int| 0 <= y < j ==> min_diff <= if a.spec_index(last_a_idx as int) < b.spec_index(y) { 
                    (b.spec_index(y) - a.spec_index(last_a_idx as int)) as nat 
                } else { 
                    (a.spec_index(last_a_idx as int) - b.spec_index(y)) as nat 
                }
        {
            let curr_diff = if a[last_a_idx] < b[j] { (b[j] - a[last_a_idx]) as nat } else { (a[last_a_idx] - b[j]) as nat };
            
            if curr_diff < min_diff {
                min_diff = curr_diff;
                witness_i = last_a_idx;
                witness_j = j;
            }
            
            j = j + 1;
        }
    }
    
    // Prove the postcondition with a brute force check
    proof {
        // The witness pair satisfies the existence requirement
        assert(exists|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() && min_diff == if a.spec_index(i) < b.spec_index(j) { (b.spec_index(j) - a.spec_index(i)) as nat } else { (a.spec_index(i) - b.spec_index(j)) as nat }) by {
            assert(0 <= witness_i < a.len());
            assert(0 <= witness_j < b.len());
        };
    }
    
    // Final brute force verification to ensure we haven't missed any pair
    let mut verify_i: usize = 0;
    while verify_i < a.len()
        invariant
            verify_i <= a.len(),
            witness_i < a.len(),
            witness_j < b.len(),
            min_diff == if a.spec_index(witness_i as int) < b.spec_index(witness_j as int) { 
                (b.spec_index(witness_j as int) - a.spec_index(witness_i as int)) as nat 
            } else { 
                (a.spec_index(witness_i as int) - b.spec_index(witness_j as int)) as nat 
            },
            forall|x: int, y: int| 0 <= x < verify_i && 0 <= y < b.len() ==> min_diff <= if a.spec_index(x) < b.spec_index(y) { 
                (b.spec_index(y) - a.spec_index(x)) as nat 
            } else { 
                (a.spec_index(x) - b.spec_index(y)) as nat 
            }
    {
        let mut verify_j: usize = 0;
        while verify_j < b.len()
            invariant
                verify_j <= b.len(),
                verify_i < a.len(),
                witness_i < a.len(),
                witness_j < b.len(),
                min_diff == if a.spec_index(witness_i as int) < b.spec_index(witness_j as int) { 
                    (b.spec_index(witness_j as int) - a.spec_index(witness_i as int)) as nat 
                } else { 
                    (a.spec_index(witness_i as int) - b.spec_index(witness_j as int)) as nat 
                },
                forall|x: int, y: int| 0 <= x < verify_i && 0 <= y < b.len() ==> min_diff <= if a.spec_index(x) < b.spec_index(y) { 
                    (b.spec_index(y) - a.spec_index(x)) as nat 
                } else { 
                    (a.spec_index(x) - b.spec_index(y)) as nat 
                },
                forall|y: int| 0 <= y < verify_j ==> min_diff <= if a.spec_index(verify_i as int) < b.spec_index(y) { 
                    (b.spec_index(y) - a.spec_index(verify_i as int)) as nat 
                } else { 
                    (a.spec_index(verify_i as int) - b.spec_index(y)) as nat 
                }
        {
            let curr_diff = if a[verify_i] < b[verify_j] { (b[verify_j] - a[verify_i]) as nat } else { (a[verify_i] - b[verify_j]) as nat };
            
            if curr_diff < min_diff {
                min_diff = curr_diff;
                witness_i = verify_i;
                witness_j = verify_j;
            }
            
            verify_j = verify_j + 1;
        }
        verify_i = verify_i + 1;
    }
    
    min_diff
}

}