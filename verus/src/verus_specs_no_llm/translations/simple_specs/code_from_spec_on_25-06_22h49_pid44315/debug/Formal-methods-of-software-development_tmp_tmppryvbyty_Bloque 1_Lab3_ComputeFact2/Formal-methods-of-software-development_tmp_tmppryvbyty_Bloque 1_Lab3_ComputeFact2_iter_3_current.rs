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

fn ComputeFact2(n: u32) -> (f: u32)
    requires
        n >= 0
    ensures
        f == factorial(n as int)
    decreases n
{
    if n <= 0 {
        proof {
            assert(factorial(n as int) == 1);
        }
        1
    } else {
        let rec_result = ComputeFact2(n - 1);
        proof {
            assert(rec_result == factorial((n - 1) as int));
            assert(factorial(n as int) == (n as int) * factorial((n - 1) as int));
            assert((n as int) * (rec_result as int) == (n as int) * factorial((n - 1) as int));
            assert((n as int) * (rec_result as int) == factorial(n as int));
        }
        n * rec_result
    }
}

}