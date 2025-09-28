// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

/* helper modified by LLM (iteration 5): Converted spec functions to proof functions and fixed sequence indexing */
// Creates a sequence of indices from 0 to n-1
proof fn index_seq(n: nat) -> Seq<usize>
    decreases n,
{
    if n == 0 {
        Seq::empty()
    } else {
        index_seq((n - 1) as nat).push((n - 1) as usize)
    }
}

// Proof that index_seq produces sorted indices
proof fn index_seq_sorted(n: nat)
    ensures
        forall|i: int, j: int| 0 <= i < j < n ==> index_seq(n)[i] < index_seq(n)[j],
    decreases n,
{
    if n > 0 {
        index_seq_sorted((n - 1) as nat);
    }
}

// Predicate to check if a sequence is sorted by the given array values
spec fn is_sorted_by(indices: Seq<usize>, a: Seq<i8>) -> bool {
    forall|i: int, j: int| 0 <= i < j < indices.len() ==> a[indices[i] as int] <= a[indices[j] as int]
}

// Helper lemma for insertion sort
proof fn insert_sorted_maintains_order(sorted: Seq<usize>, a: Seq<i8>, new_index: usize, value: i8)
    requires
        sorted.len() + 1 == a.len(),
        is_sorted_by(sorted, a),
        0 <= new_index < a.len(),
        forall|k: int| 0 <= k < sorted.len() ==> 0 <= sorted[k] < a.len(),
        new_index < a.len(),
    ensures
        exists|pos: int| 
            0 <= pos <= sorted.len() && 
            is_sorted_by(sorted.insert(pos, new_index), a),
    decreases sorted.len(),
{
    // Proof by induction on the sorted sequence
    if sorted.len() == 0 {
        // Base case: empty sequence, insert at position 0
        assert(is_sorted_by(sorted.insert(0, new_index), a));
    } else {
        // Recursive case: find the correct position to insert
        let first_val = a[sorted[0] as int];
        if value <= first_val {
            // Insert at beginning
            assert(is_sorted_by(sorted.insert(0, new_index), a));
        } else {
            // Insert in the tail
            let tail = sorted.subrange(1, sorted.len() as int);
            insert_sorted_maintains_order(tail, a, new_index, value);
            assert(is_sorted_by(sorted.insert(sorted.len() as int, new_index), a));
        }
    }
}

// </vc-helpers>

// <vc-spec>
fn argsort(a: Vec<i8>) -> (result: Vec<usize>)
    ensures 
        result.len() == a.len(),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> #[trigger] a@[result@[i] as int] <= #[trigger] a@[result@[j] as int],
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 5): Fixed sequence indexing syntax */
    let n = a.len();
    let mut result = Vec::<usize>::new();
    
    let mut i: usize = 0;
    while i < n
        invariant
            result.len() == i,
            is_sorted_by(result@, a@),
            forall|k: int| 0 <= k < result.len() ==> 0 <= result@[k] < a.len(),
        decreases n - i,
    {
        let current_index = i;
        let current_value = a[current_index];
        
        // Find the position to insert the current index
        let mut pos: usize = 0;
        let mut j: usize = 0;
        
        while j < result.len()
            invariant
                0 <= j <= result.len(),
                0 <= pos <= j,
                forall|k: int| 0 <= k < j ==> a[result@[k] as int] <= current_value || k < pos,
                forall|k: int| pos <= k < j ==> current_value < a[result@[k] as int],
            decreases result.len() - j,
        {
            if a[result[j]] <= current_value {
                pos = j + 1;
            }
            j = j + 1;
        }
        
        // Insert the current index at the found position
        proof {
            insert_sorted_maintains_order(result@, a@, current_index, current_value);
        }
        result.insert(pos, current_index);
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}