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
        n as int + fSum((n - 1) as nat)
    }
}

fn problem6(n: nat) -> (a: int)
    ensures
        a == fSum(n)
    decreases n
{
    if n == 0 {
        0
    } else {
        assert(n > 0);
        let prev = problem6(n - 1);
        assert(prev == fSum((n - 1) as nat));
        let result = prev + n as int;
        assert(result == n as int + fSum((n - 1) as nat));
        assert(result == fSum(n));
        result
    }
}

}