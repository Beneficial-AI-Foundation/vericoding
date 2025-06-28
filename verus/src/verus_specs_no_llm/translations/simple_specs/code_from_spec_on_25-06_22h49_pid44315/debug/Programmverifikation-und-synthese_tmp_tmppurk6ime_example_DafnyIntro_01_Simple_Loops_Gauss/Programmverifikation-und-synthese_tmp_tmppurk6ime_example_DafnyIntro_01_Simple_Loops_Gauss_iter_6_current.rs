However, Verus may need help with the arithmetic reasoning. Let me fix this by adding proper proof annotations and ensuring the invariant maintenance is clear:

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Gauss(n: int) -> (sum: int)
    requires
        n >= 0
    ensures
        sum == n*(n+1)/2
{
    if n == 0 {
        0
    } else {
        let mut i: int = 1;
        let mut sum: int = 0;
        
        while i <= n
            invariant
                1 <= i <= n + 1,
                sum == (i - 1) * i / 2
        {
            // Before update: sum == (i-1) * i / 2
            // After adding i: sum + i == (i-1) * i / 2 + i
            // Simplify: (i-1) * i / 2 + i = (i-1) * i / 2 + 2*i/2 = ((i-1) * i + 2*i) / 2
            //          = (i * (i-1) + 2*i) / 2 = (i * (i-1+2)) / 2 = i * (i+1) / 2
            
            sum = sum + i;
            i = i + 1;
            
            // Now i is incremented, so the new invariant should be:
            // sum == (new_i - 1) * new_i / 2 = i * (i+1) / 2 from above
        }
        
        // Loop exit: i == n + 1, so sum == (n+1-1) * (n+1) / 2 = n * (n+1) / 2
        sum
    }
}

}