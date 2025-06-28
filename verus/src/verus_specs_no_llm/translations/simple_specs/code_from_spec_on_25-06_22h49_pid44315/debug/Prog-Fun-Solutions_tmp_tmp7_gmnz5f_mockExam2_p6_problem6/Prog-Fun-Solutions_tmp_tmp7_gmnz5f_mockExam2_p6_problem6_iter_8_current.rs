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
        prev + n as int
    }
}

}