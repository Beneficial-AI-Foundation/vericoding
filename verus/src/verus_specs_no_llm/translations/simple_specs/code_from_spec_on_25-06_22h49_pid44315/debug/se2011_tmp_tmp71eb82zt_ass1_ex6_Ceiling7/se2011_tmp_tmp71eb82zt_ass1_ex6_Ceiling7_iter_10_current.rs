use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Ceiling7(n: nat) -> (k: nat)
    ensures
        k % 7 == 0,
        k >= n,
        k < n + 7
{
    if n % 7 == 0 {
        n
    } else {
        let remainder = n % 7;
        let k = n + (7 - remainder);
        
        // Proof annotations to help verification
        assert(remainder > 0);
        assert(remainder < 7);
        assert(7 - remainder > 0);
        assert(7 - remainder <= 7);
        assert(k == n + (7 - remainder));
        assert(k >= n);
        assert(k < n + 7);
        
        // Prove k % 7 == 0
        assert(k == n + 7 - remainder);
        assert(k == (n - remainder) + 7);
        assert((n - remainder) % 7 == 0) by {
            assert(n % 7 == remainder);
        };
        assert(k % 7 == ((n - remainder) + 7) % 7);
        assert(k % 7 == (n - remainder) % 7);
        assert(k % 7 == 0);
        
        k
    }
}

}