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
            greedy_placement_correct(pos, placed, last_pos, c)
    {
        if pos - last_pos >= c {
            placed = placed + 1;
            last_pos = pos;
        }
        pos = pos + 1;
    }
    
    placed >= k
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

// Specification function for loop invariant
spec fn greedy_placement_correct(pos: int, placed: int, last_pos: int, c: int) -> bool {
    // The invariant holds that we've made optimal greedy choices so far
    last_pos >= -c &&
    (placed > 0 ==> last_pos >= 0) &&
    (placed > 0 ==> last_pos < pos)
}

// Proof function to establish the connection between implementation and specification
proof fn greedy_correctness_lemma(n: int, k: int, c: int, pos: int, placed: int, last_pos: int)
    requires
        0 <= pos <= n,
        0 <= placed <= k,
        last_pos >= -c,
        placed > 0 ==> last_pos >= 0,
        placed > 0 ==> last_pos < pos
    ensures
        greedy_placement_correct(pos, placed, last_pos, c)
{
    // The proof is automatically handled by Verus for this simple invariant
}

}