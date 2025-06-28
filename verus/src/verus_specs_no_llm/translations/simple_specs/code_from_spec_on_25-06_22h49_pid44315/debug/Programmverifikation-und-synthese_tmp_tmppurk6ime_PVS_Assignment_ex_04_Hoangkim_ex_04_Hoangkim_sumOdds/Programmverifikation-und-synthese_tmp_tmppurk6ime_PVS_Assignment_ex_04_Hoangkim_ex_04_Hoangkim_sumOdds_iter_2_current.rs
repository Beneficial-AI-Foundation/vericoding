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
        assert(total == (i - 1) * (i - 1) + (2 * i - 1));
        assert(total == (i - 1) * (i - 1) + 2 * i - 1);
        assert(total == i * i - 2 * i + 1 + 2 * i - 1);
        assert(total == i * i);
        
        i = i + 1;
    }
    
    // When loop exits, i == n + 1, so total == (n + 1 - 1) * (n + 1 - 1) == n * n
    assert(i == n + 1);
    assert(total == (i - 1) * (i - 1));
    assert(total == n * n);
    
    total
}

}