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
    // Initialize with the first pair
    let mut min_diff: nat = if a[0] < b[0] { (b[0] - a[0]) as nat } else { (a[0] - b[0]) as nat };
    let mut witness_i: usize = 0;
    let mut witness_j: usize = 0;
    
    // Simple brute force approach to ensure correctness
    let mut i: usize = 0;
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
            // All pairs with first element from a[0..i] have been considered
            forall|x: int, y: int| 0 <= x < i && 0 <= y < b.len() ==> min_diff <= if a.spec_index(x) < b.spec_index(y) { 
                (b.spec_index(y) - a.spec_index(x)) as nat 
            } else { 
                (a.spec_index(x) - b.spec_index(y)) as nat 
            }
    {
        let mut j: usize = 0;
        while j < b.len()
            invariant
                j <= b.len(),
                i < a.len(),
                witness_i < a.len(),
                witness_j < b.len(),
                min_diff == if a.spec_index(witness_i as int) < b.spec_index(witness_j as int) { 
                    (b.spec_index(witness_j as int) - a.spec_index(witness_i as int)) as nat 
                } else { 
                    (a.spec_index(witness_i as int) - b.spec_index(witness_j as int)) as nat 
                },
                // All pairs with first element from a[0..i] have been considered
                forall|x: int, y: int| 0 <= x < i && 0 <= y < b.len() ==> min_diff <= if a.spec_index(x) < b.spec_index(y) { 
                    (b.spec_index(y) - a.spec_index(x)) as nat 
                } else { 
                    (a.spec_index(x) - b.spec_index(y)) as nat 
                },
                // All pairs (a[i], b[0..j]) have been considered
                forall|y: int| 0 <= y < j ==> min_diff <= if a.spec_index(i as int) < b.spec_index(y) { 
                    (b.spec_index(y) - a.spec_index(i as int)) as nat 
                } else { 
                    (a.spec_index(i as int) - b.spec_index(y)) as nat 
                }
        {
            let curr_diff = if a[i] < b[j] { (b[j] - a[i]) as nat } else { (a[i] - b[j]) as nat };
            
            if curr_diff < min_diff {
                min_diff = curr_diff;
                witness_i = i;
                witness_j = j;
            }
            
            j = j + 1;
        }
        i = i + 1;
    }
    
    min_diff
}

}