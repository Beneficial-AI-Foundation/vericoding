use builtin::*;
use builtin_macros::*;

verus! {

// Define the spec function f that was referenced but missing
spec fn f(n: nat) -> int {
    n as int
}

fn main() {
}

fn problem5(n: nat) -> (x: int)
    ensures
        x == f(n)
{
    // Add explicit proof that the cast preserves the value
    proof {
        assert(n as int == f(n));
    }
    n as int
}

}