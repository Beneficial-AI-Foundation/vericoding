The problem is that when the loop exits (when `i == n + 1`), we have `sum == (n+1-1)*(n+1)/2 = n*(n+1)/2`, but the invariant as written doesn't properly track the cumulative sum of integers from 1 to the current position.

Let me fix this by correcting the loop invariant:

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
            sum = sum + i;
            i = i + 1;
        }
        sum
    }
}

}

Wait, let me reconsider this. The invariant should state that `sum` equals the sum of integers from 1 to `i-1`. The formula for the sum of integers from 1 to k is k*(k+1)/2. So for the sum from 1 to (i-1), it should be (i-1)*i/2.

Let me trace through this:
- Initially: i=1, sum=0. Invariant: sum == (1-1)*1/2 = 0 ✓
- After first iteration: i=2, sum=1. Invariant: sum == (2-1)*2/2 = 1 ✓
- After second iteration: i=3, sum=3. Invariant: sum == (3-1)*3/2 = 3 ✓

This looks correct. The issue might be that Verus needs help proving the arithmetic. Let me add some proof annotations:

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
            sum = sum + i;
            i = i + 1;
        }
        
        assert(i == n + 1);
        assert(sum == n * (n + 1) / 2);
        sum
    }
}

}