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
                0 <= i <= n + 1,
                sum == (i - 1) * i / 2
        {
            sum = sum + i;
            i = i + 1;
        }
        sum
    }
}

}