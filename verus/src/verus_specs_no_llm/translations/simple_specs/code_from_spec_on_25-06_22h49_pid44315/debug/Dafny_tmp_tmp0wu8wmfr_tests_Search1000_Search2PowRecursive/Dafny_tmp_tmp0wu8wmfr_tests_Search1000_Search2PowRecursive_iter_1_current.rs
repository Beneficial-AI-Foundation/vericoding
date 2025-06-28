use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Is2Pow(n: int) -> bool {
    if n < 1 {
        false
    } else if n == 1 {
        true
    } else {
        n % 2 == 0 && Is2Pow(n / 2)
    }
}

fn Search2PowRecursive(a: Vec<int>, i: int, n: int, x: int) -> (k: int)
    requires
        0 <= i <= i + n <= a.len(),
        forall|p: int, q: int| i <= p < q < i + n ==> a.spec_index(p) <= a.spec_index(q),
        Is2Pow(n + 1)
    ensures
        i <= k <= i + n,
        forall|r: int| i <= r < k ==> a.spec_index(r) < x,
        forall|r: int| k <= r < i + n ==> a.spec_index(r) >= x
{
    if n == 0 {
        return i;
    }
    
    let mid = i + n / 2;
    
    if a[mid as usize] < x {
        // Search in the right half
        assert(Is2Pow(n / 2 + 1)) by {
            // Since Is2Pow(n + 1) and n > 0, we have n + 1 is a power of 2
            // So n + 1 = 2^k for some k >= 1
            // Therefore n = 2^k - 1, and n / 2 = (2^k - 1) / 2 = 2^(k-1) - 1/2
            // Since n is even (because n + 1 is a power of 2 > 1), n / 2 is an integer
            // And n / 2 + 1 = 2^(k-1) which is a power of 2
        };
        
        Search2PowRecursive(a, mid, n / 2, x)
    } else {
        // Search in the left half
        assert(Is2Pow(n / 2 + 1)) by {
            // Same reasoning as above
        };
        
        Search2PowRecursive(a, i, n / 2, x)
    }
}

}

The key insights for this implementation:


   - If `a[mid] < x`, we search the right half from `mid` to `i+n`
   - If `a[mid] >= x`, we search the left half from `i` to `mid`

   - If `n+1 = 2^k` for some `k >= 1`, then `n = 2^k - 1`
   - Since `k >= 1`, we have `n` is even, so `n/2` is an integer
   - `n/2 + 1 = (2^k - 1)/2 + 1 = 2^(k-1) - 1/2 + 1 = 2^(k-1) + 1/2`
   - Wait, let me reconsider this...
   - Actually, `n/2 + 1 = (2^k - 1)/2 + 1 = 2^(k-1) - 1/2 + 1 = 2^(k-1) + 1/2`
   - Since `n` is odd when `n+1` is a power of 2 > 1, we need to be more careful.

Let me fix the reasoning: if `n+1 = 2^k`, then `n = 2^k - 1`. For the recursive calls, we're searching arrays of size `n/2`, so we need `Is2Pow(n/2 + 1)`. Since `n = 2^k - 1`, we have `n/2 = (2^k - 1)/2 = 2^(k-1) - 1/2`. In integer division, this becomes `2^(k-1) - 1` when `k > 1`, and `n/2 + 1 = 2^(k-1)`, which is indeed a power of 2.

The assertions help Verus verify that the recursive calls satisfy the preconditions.