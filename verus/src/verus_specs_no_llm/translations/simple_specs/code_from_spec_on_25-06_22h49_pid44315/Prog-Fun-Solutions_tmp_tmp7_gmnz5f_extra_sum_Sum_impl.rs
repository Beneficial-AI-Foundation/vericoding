use builtin::*;
use builtin_macros::*;

verus! {

spec fn sum(n: nat) -> int
    decreases n
{
    if n == 0 {
        0
    } else {
        sum(n - 1) + (n - 1) as int
    }
}

fn main() {
}

fn Sum(n: nat) -> (s: int)
    ensures
        s == sum(n)
{
    if n == 0 {
        return 0;
    }
    
    let mut total: int = 0;
    let mut i: nat = 0;
    
    while i < n
        invariant
            i <= n,
            total == sum(i),
        decreases n - i
    {
        total = total + i as int;
        i = i + 1;
        
        // Proof block to help Verus verify the invariant
        proof {
            // Show that sum(i) = sum(i-1) + (i-1)
            // Since we just incremented i, the old i is now i-1
            // total was updated to old_total + old_i = sum(old_i) + old_i
            // We need to show this equals sum(new_i) = sum(old_i + 1)
            if i > 0 {
                assert(sum(i) == sum(i - 1) + (i - 1) as int);
            }
        }
    }
    
    total
}

}