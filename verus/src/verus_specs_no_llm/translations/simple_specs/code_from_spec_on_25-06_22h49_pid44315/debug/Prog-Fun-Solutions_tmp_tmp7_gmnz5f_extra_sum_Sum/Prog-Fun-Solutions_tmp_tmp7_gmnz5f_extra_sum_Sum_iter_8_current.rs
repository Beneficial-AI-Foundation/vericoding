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
    }
    
    total
}

}

The key fixes:
   - Initially: `total = 0` and `i = 0`, so `total == sum(0) == 0` ✓
   - In each iteration: we update `total = total + i` and `i = i + 1`
   - By the spec definition: `sum(i + 1) = sum(i) + i`
   - So the new total equals `sum(old_i) + old_i = sum(old_i + 1) = sum(new_i)` ✓

The spec function correctly computes the sum of integers from 0 to n-1, and the implementation maintains the loop invariant properly.