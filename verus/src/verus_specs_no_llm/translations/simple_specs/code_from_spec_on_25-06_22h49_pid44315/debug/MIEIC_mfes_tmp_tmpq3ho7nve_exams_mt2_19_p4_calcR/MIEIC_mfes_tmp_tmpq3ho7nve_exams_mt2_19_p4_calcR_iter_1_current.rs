use builtin::*;
use builtin_macros::*;

verus! {

// Define the spec function R
spec fn R(n: nat) -> nat {
    n
}

fn main() {
}

fn calcR(n: nat) -> (r: nat)
    ensures
        r == R(n)
{
    n
}

}