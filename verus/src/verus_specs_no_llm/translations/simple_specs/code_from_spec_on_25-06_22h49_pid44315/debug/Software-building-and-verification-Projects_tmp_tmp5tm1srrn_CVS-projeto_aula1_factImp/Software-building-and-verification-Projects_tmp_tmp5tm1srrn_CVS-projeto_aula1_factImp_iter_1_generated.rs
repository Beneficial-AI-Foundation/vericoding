use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn factorial(n: int) -> int
    decreases n
{
    if n <= 0 {
        1
    } else {
        n * factorial(n - 1)
    }
}

fn factImp(n: int) -> (r: int)
    requires n >= 0
    ensures r == factorial(n)
    ensures r >= 1
{
    if n <= 0 {
        1
    } else {
        let mut result = 1;
        let mut i = 1;
        
        while i <= n
            invariant 1 <= i <= n + 1
            invariant result == factorial(i - 1)
        {
            result = result * i;
            i = i + 1;
        }
        
        result
    }
}

}