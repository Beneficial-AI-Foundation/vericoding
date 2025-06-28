use builtin::*;
use builtin_macros::*;

verus! {

spec fn factorial(n: int) -> int
    decreases n
{
    if n <= 0 {
        1
    } else {
        n * factorial(n - 1)
    }
}

fn main() {
}

fn ComputeFact2(n: int) -> (f: int)
    requires
        n >= 0
    ensures
        f == factorial(n)
    decreases n
{
    if n <= 0 {
        1
    } else {
        n * ComputeFact2(n - 1)
    }
}

}