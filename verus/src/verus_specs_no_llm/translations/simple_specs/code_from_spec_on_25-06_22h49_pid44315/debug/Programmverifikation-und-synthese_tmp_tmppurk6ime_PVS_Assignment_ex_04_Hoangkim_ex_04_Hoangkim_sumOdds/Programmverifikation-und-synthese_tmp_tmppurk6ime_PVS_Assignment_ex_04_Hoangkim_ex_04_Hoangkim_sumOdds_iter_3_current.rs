use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn sumOdds(n: nat) -> (sum: nat)
    requires
        n > 0
    ensures
        sum == n * n
{
    let mut i: nat = 1;
    let mut total: nat = 0;
    
    while i <= n
        invariant
            1 <= i <= n + 1,
            total == (i - 1) * (i - 1)
    {
        let odd_number = 2 * i - 1;
        total = total + odd_number;
        
        // Proof that the invariant is maintained
        // We need to show that total == i * i after the update
        // total was (i-1)² before, now it's (i-1)² + (2i-1)
        // We need to prove that (i-1)² + (2i-1) == i²
        assert(total == (i - 1) * (i - 1) + (2 * i - 1));
        
        // Expand (i-1)²
        assert((i - 1) * (i - 1) == i * i - 2 * i + 1);
        
        // So total = i² - 2i + 1 + 2i - 1 = i²
        assert(total == i * i - 2 * i + 1 + 2 * i - 1);
        assert(total == i * i);
        
        i = i + 1;
        
        // After incrementing i, we need total == (i-1) * (i-1)
        // Since total == old_i * old_i and new_i = old_i + 1
        // We have total == (new_i - 1) * (new_i - 1)
    }
    
    // When loop exits, i == n + 1, so total == (n + 1 - 1)² == n²
    assert(i == n + 1);
    assert(total == (i - 1) * (i - 1));
    assert(total == n * n);
    
    total
}

}