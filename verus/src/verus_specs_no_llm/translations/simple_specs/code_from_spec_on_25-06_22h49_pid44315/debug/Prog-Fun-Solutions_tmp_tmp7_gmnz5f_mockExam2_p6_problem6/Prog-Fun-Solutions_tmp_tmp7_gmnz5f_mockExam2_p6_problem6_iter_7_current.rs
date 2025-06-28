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
        assert(fSum(0) == 0);
        0
    } else {
        let prev = problem6(n - 1);
        assert(prev == fSum(n - 1));
        let result = prev + n as int;
        assert(result == fSum(n - 1) + n as int);
        assert(fSum(n) == n as int + fSum(n - 1));
        assert(result == fSum(n));
        result
    }
}

}