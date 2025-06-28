use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn f(n: nat) -> nat {
    n
}

fn mod(n: nat) -> (a: nat)
    ensures
        a == f(n)
{
    n
}

}