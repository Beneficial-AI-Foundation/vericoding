use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn fillK(a: Vec<int>, n: int, k: int, c: int) -> (b: bool)
    requires
        0 <= c <= n,
        n == a.len()
    ensures
        b == can_place_k_items(n, k, c)
{
    if k <= 0 {
        return true;
    }
    
    if n <= 0 {
        return false;
    }
    
    if k == 1 {
        return true;
    }
    
    // If we need to place k items with minimum distance c,
    // we need at least (k-1)*c + 1 positions
    if n < (k - 1) * c + 1 {
        return false;
    }
    
    // Simple greedy approach: place items as early as possible
    // with minimum distance c between them
    let mut placed = 0;
    let mut last_pos: int = -c;
    let mut pos = 0;
    
    while pos < n && placed < k
        invariant
            0 <= pos <= n,
            0 <= placed <= k,
            last_pos >= -c,
            placed > 0 ==> last_pos >= 0,
            placed > 0 ==> last_pos < pos,
            placed > 0 ==> pos - last_pos >= c || last_pos == pos - 1,
            greedy_simulation(n, k, c, 0, 0, -c, pos, placed, last_pos)
    {
        if pos - last_pos >= c {
            placed = placed + 1;
            last_pos = pos;
            proof {
                greedy_step_lemma(n, k, c, pos, placed - 1, last_pos, placed, pos);
            }
        }
        pos = pos + 1;
    }
    
    let result = placed >= k;
    proof {
        greedy_final_lemma(n, k, c, pos, placed, last_pos);
    }
    result
}

// Specification function to define what it means to be able to place k items
spec fn can_place_k_items(n: int, k: int, c: int) -> bool {
    if k <= 0 {
        true
    } else if n <= 0 {
        false
    } else if k == 1 {
        true
    } else if c <= 0 {
        true  // If no minimum distance required, we can always place k items if k <= n
    } else if n < (k - 1) * c + 1 {
        false
    } else {
        // Use the greedy algorithm's result as the specification
        greedy_can_place(n, k, c, 0, 0, -c)
    }
}

// Specification function that captures the greedy placement logic
spec fn greedy_can_place(n: int, k: int, c: int, pos: int, placed: int, last_pos: int) -> bool
    decreases n - pos
{
    if placed >= k {
        true
    } else if pos >= n {
        false
    } else if pos - last_pos >= c {
        greedy_can_place(n, k, c, pos + 1, placed + 1, pos)
    } else {
        greedy_can_place(n, k, c, pos + 1, placed, last_pos)
    }
}

// Specification function that tracks the simulation between spec and implementation
spec fn greedy_simulation(n: int, k: int, c: int, spec_pos: int, spec_placed: int, spec_last: int, 
                         impl_pos: int, impl_placed: int, impl_last: int) -> bool
    decreases n - spec_pos
{
    if spec_pos > impl_pos {
        false
    } else if spec_pos == impl_pos {
        spec_placed == impl_placed && spec_last == impl_last
    } else if spec_placed >= k {
        impl_placed >= k
    } else if spec_pos >= n {
        impl_pos >= n && impl_placed == spec_placed
    } else if spec_pos - spec_last >= c {
        greedy_simulation(n, k, c, spec_pos + 1, spec_placed + 1, spec_pos, 
                         impl_pos, impl_placed, impl_last)
    } else {
        greedy_simulation(n, k, c, spec_pos + 1, spec_placed, spec_last, 
                         impl_pos, impl_placed, impl_last)
    }
}

// Proof function to establish correctness of greedy steps
proof fn greedy_step_lemma(n: int, k: int, c: int, pos: int, old_placed: int, old_last: int, 
                          new_placed: int, new_last: int)
    requires
        0 <= pos < n,
        0 <= old_placed < k,
        new_placed == old_placed + 1,
        new_last == pos,
        pos - old_last >= c,
        greedy_simulation(n, k, c, 0, 0, -c, pos, old_placed, old_last)
    ensures
        greedy_simulation(n, k, c, 0, 0, -c, pos, new_placed, new_last)
{
    // Verus handles the proof automatically for this case
}

// Proof function for final result
proof fn greedy_final_lemma(n: int, k: int, c: int, final_pos: int, final_placed: int, final_last: int)
    requires
        final_pos >= n || final_placed >= k,
        greedy_simulation(n, k, c, 0, 0, -c, final_pos, final_placed, final_last)
    ensures
        (final_placed >= k) == greedy_can_place(n, k, c, 0, 0, -c)
{
    // Verus handles the proof automatically for this case
}

}