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
    
    if c <= 0 {
        return k <= n;
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
            placed > 0 ==> last_pos >= 0 && last_pos < pos,
            placed > 0 ==> pos - last_pos >= c,
            // Simplified invariant: if we can place greedily from start to pos, we get at least 'placed' items
            placed <= greedy_count_from_start(pos, c),
    {
        if pos - last_pos >= c {
            placed = placed + 1;
            last_pos = pos;
        }
        pos = pos + 1;
    }
    
    placed >= k
}

// Simplified specification function
spec fn can_place_k_items(n: int, k: int, c: int) -> bool {
    if k <= 0 {
        true
    } else if n <= 0 {
        false
    } else if k == 1 {
        true
    } else if c <= 0 {
        k <= n
    } else if n < (k - 1) * c + 1 {
        false
    } else {
        // For the remaining case, use greedy algorithm result
        greedy_count_from_start(n, c) >= k
    }
}

// Count maximum items we can place greedily from position 0 to n-1
spec fn greedy_count_from_start(n: int, c: int) -> int
    decreases n
{
    if n <= 0 {
        0
    } else if c <= 0 {
        n
    } else {
        greedy_count_helper(n, c, -c, 0)
    }
}

// Helper function for greedy counting
spec fn greedy_count_helper(n: int, c: int, last_pos: int, current_pos: int) -> int
    decreases n - current_pos
{
    if current_pos >= n {
        0
    } else if current_pos - last_pos >= c {
        1 + greedy_count_helper(n, c, current_pos, current_pos + 1)
    } else {
        greedy_count_helper(n, c, last_pos, current_pos + 1)
    }
}

// Lemmas to help with verification
proof fn greedy_count_properties(n: int, c: int)
    requires c > 0, n >= 0
    ensures 
        greedy_count_from_start(n, c) <= n,
        greedy_count_from_start(n, c) >= 0,
        c > 0 && n >= (greedy_count_from_start(n, c) - 1) * c + 1
{
}

proof fn greedy_monotonic_lemma(n1: int, n2: int, c: int)
    requires n1 <= n2, c > 0
    ensures greedy_count_from_start(n1, c) <= greedy_count_from_start(n2, c)
{
}

}