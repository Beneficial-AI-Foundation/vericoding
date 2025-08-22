use vstd::prelude::*;

verus! {

// Count how many times a specific value appears in the list
spec fn count_val(val: i32, xs: Seq<i32>) -> nat
    decreases xs.len()
{
    if xs.len() == 0 {
        0nat
    } else {
        let rest = count_val(val, xs.drop_first());
        if xs.first() == val {
            rest + 1
        } else {
            rest
        }
    }
}

// Check whether one list is a subsequence of another (preserving relative order)
spec fn is_subsequence(xs: Seq<i32>, ys: Seq<i32>) -> bool
    decreases xs.len() + ys.len()
{
    if xs.len() == 0 {
        true
    } else if ys.len() == 0 {
        false
    } else {
        let x = xs.first();
        let y = ys.first();
        if x == y {
            is_subsequence(xs.drop_first(), ys.drop_first())
        } else {
            is_subsequence(xs, ys.drop_first())
        }
    }
}

// Helper function to filter out zeros
spec fn filter_nonzeros(xs: Seq<i32>) -> Seq<i32>
    decreases xs.len()
{
    if xs.len() == 0 {
        seq![]
    } else {
        let first = xs.first();
        let rest = filter_nonzeros(xs.drop_first());
        if first != 0 {
            seq![first] + rest
        } else {
            rest
        }
    }
}

// Helper function to filter zeros
spec fn filter_zeros(xs: Seq<i32>) -> Seq<i32>
    decreases xs.len()
{
    if xs.len() == 0 {
        seq![]
    } else {
        let first = xs.first();
        let rest = filter_zeros(xs.drop_first());
        if first == 0 {
            seq![first] + rest
        } else {
            rest
        }
    }
}

// Check if all elements in a sequence are zeros
spec fn all_zeros(xs: Seq<i32>) -> bool
    decreases xs.len()
{
    if xs.len() == 0 {
        true
    } else {
        xs.first() == 0 && all_zeros(xs.drop_first())
    }
}

// Drop elements while they satisfy a predicate
spec fn drop_while_nonzero(xs: Seq<i32>) -> Seq<i32>
    decreases xs.len()
{
    if xs.len() == 0 {
        seq![]
    } else if xs.first() != 0 {
        drop_while_nonzero(xs.drop_first())
    } else {
        xs
    }
}

spec fn move_zeroes_precond(xs: Seq<i32>) -> bool {
    true
}

spec fn move_zeroes_postcond(xs: Seq<i32>, result: Seq<i32>) -> bool {
    // 1. All non-zero elements must maintain their relative order
    is_subsequence(filter_nonzeros(xs), result) &&
    
    // 2. All zeroes must be located at the end of the output list
    all_zeros(drop_while_nonzero(result)) &&
    
    // 3. The output must contain the same number of elements,
    //    and the number of zeroes must remain unchanged
    count_val(0, xs) == count_val(0, result) &&
    xs.len() == result.len()
}

// Lemma: appending non-zero element preserves filter_nonzeros property
proof fn lemma_filter_nonzeros_push(xs: Seq<i32>, x: i32)
    requires x != 0
    ensures filter_nonzeros(xs.push(x)) == filter_nonzeros(xs).push(x)
    decreases xs.len()
{
    if xs.len() == 0 {
        assert(xs.push(x) == seq![x]);
        assert(filter_nonzeros(seq![x]) == seq![x]);
        assert(filter_nonzeros(xs) == seq![]);
    } else {
        let first = xs.first();
        let rest = xs.drop_first();
        assert(xs == seq![first] + rest);
        assert(xs.push(x) == seq![first] + rest.push(x));
        lemma_filter_nonzeros_push(rest, x);
    }
}

// Lemma: appending zero doesn't change filter_nonzeros
proof fn lemma_filter_nonzeros_push_zero(xs: Seq<i32>)
    ensures filter_nonzeros(xs.push(0)) == filter_nonzeros(xs)
    decreases xs.len()
{
    if xs.len() == 0 {
        // Base case
    } else {
        lemma_filter_nonzeros_push_zero(xs.drop_first());
    }
}

// Lemma: count_val distributes over push
proof fn lemma_count_val_push(val: i32, xs: Seq<i32>, x: i32)
    ensures count_val(val, xs.push(x)) == count_val(val, xs) + if x == val { 1nat } else { 0nat }
    decreases xs.len()
{
    if xs.len() == 0 {
        // Base case
    } else {
        lemma_count_val_push(val, xs.drop_first(), x);
    }
}

// Lemma: all zeros starting from some point
proof fn lemma_all_zeros_suffix(xs: Seq<i32>, zeros: Seq<i32>)
    requires all_zeros(zeros)
    ensures all_zeros(drop_while_nonzero(xs + zeros))
    decreases xs.len()
{
    if xs.len() == 0 {
        assert(xs + zeros == zeros);
    } else if xs.first() != 0 {
        lemma_all_zeros_suffix(xs.drop_first(), zeros);
    } else {
        // xs.first() == 0, so drop_while_nonzero stops here
    }
}

fn move_zeroes(xs: Vec<i32>) -> (result: Vec<i32>)
    requires move_zeroes_precond(xs@)
    ensures move_zeroes_postcond(xs@, result@)
{
    let mut result = Vec::new();
    let mut zero_count = 0;
    
    // First pass: collect non-zero elements
    let mut i = 0;
    while i < xs.len()
        invariant 
            0 <= i <= xs.len(),
            result.len() + zero_count == i,
            filter_nonzeros(xs@.subrange(0, i as int)) == result@,
            count_val(0, xs@.subrange(0, i as int)) == zero_count,
            is_subsequence(result@, xs@)
    {
        if xs[i] != 0 {
            result.push(xs[i]);
            proof {
                lemma_filter_nonzeros_push(xs@.subrange(0, i as int), xs@[i as int]);
                lemma_count_val_push(0, xs@.subrange(0, i as int), xs@[i as int]);
            }
        } else {
            zero_count += 1;
            proof {
                lemma_filter_nonzeros_push_zero(xs@.subrange(0, i as int));
                lemma_count_val_push(0, xs@.subrange(0, i as int), xs@[i as int]);
            }
        }
        i += 1;
    }
    
    // Second pass: append zeros
    let mut j = 0;
    while j < zero_count
        invariant 
            0 <= j <= zero_count,
            result.len() == filter_nonzeros(xs@).len() + j,
            filter_nonzeros(xs@) == result@.subrange(0, filter_nonzeros(xs@).len() as int),
            forall|k: int| filter_nonzeros(xs@).len() <= k < result.len() ==> result@[k] == 0,
            is_subsequence(filter_nonzeros(xs@), result@)
    {
        result.push(0);
        j += 1;
    }
    
    proof {
        // Prove postconditions
        assert(result@.len() == filter_nonzeros(xs@).len() + zero_count);
        assert(filter_nonzeros(xs@).len() + count_val(0, xs@) == xs@.len());
        
        // Prove is_subsequence(filter_nonzeros(xs@), result@)
        assert(is_subsequence(filter_nonzeros(xs@), result@));
        
        // Prove all_zeros(drop_while_nonzero(result@))
        let nonzeros = result@.subrange(0, filter_nonzeros(xs@).len() as int);
        let zeros = result@.subrange(filter_nonzeros(xs@).len() as int, result@.len() as int);
        
        assert(result@ == nonzeros + zeros);
        assert(forall|k: int| 0 <= k < zeros.len() ==> zeros[k] == 0);
        assert(all_zeros(zeros));
        
        lemma_all_zeros_suffix(nonzeros, zeros);
        
        // Prove count preservation
        assert(count_val(0, result@) == count_val(0, xs@));
    }
    
    result
}

/* code modified by LLM (iteration 1): Added simple print_container implementation and fixed main function */
fn print_container(v: Vec<i32>) {
    // Simple implementation for demonstration
}

fn main() {
    let test_vec = vec![0, 1, 0, 3, 12];
    let result = move_zeroes(test_vec);
    print_container(result);
}

}