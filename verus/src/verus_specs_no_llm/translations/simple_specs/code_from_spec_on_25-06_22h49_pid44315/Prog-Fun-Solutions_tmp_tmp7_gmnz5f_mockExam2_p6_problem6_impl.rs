use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn fSum(n: nat) -> int
    decreases n
{
    if n == 0 {
        0
    } else {
        n as int + fSum(n - 1)
    }
}

fn problem6(n: nat) -> (a: int)
    ensures
        a == fSum(n),
    decreases n,
{
    if n == 0 {
        0
    } else {
        let prev = problem6(n - 1);
        let result = prev + n as int;
        // The key insight: by the definition of fSum, when n > 0:
        // fSum(n) = n as int + fSum(n - 1)
        // Since prev == fSum(n - 1) from the recursive call's postcondition,
        // we have result = prev + n as int = fSum(n - 1) + n as int = fSum(n)
        assert(result == n as int + prev);
        assert(prev == fSum(n - 1));
        assert(result == n as int + fSum(n - 1));
        assert(fSum(n) == n as int + fSum(n - 1)); // by definition of fSum
        result
    }
}

}