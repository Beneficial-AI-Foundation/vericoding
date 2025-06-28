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
        proof {
            assert(factorial(n) == 1);
        }
        1
    } else {
        let rec_result = ComputeFact2(n - 1);
        proof {
            assert(rec_result == factorial(n - 1));
            assert(factorial(n) == n * factorial(n - 1));
            assert(n * rec_result == n * factorial(n - 1));
            assert(n * rec_result == factorial(n));
        }
        n * rec_result
    }
}

}