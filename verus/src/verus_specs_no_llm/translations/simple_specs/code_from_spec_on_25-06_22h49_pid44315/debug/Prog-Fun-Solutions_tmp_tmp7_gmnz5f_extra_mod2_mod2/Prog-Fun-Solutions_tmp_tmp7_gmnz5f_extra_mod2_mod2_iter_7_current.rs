use builtin::*;
use builtin_macros::*;

verus! {

spec fn f2(n: nat) -> nat {
    n % 2
}

fn main() {
}

fn mod2(n: nat) -> (a: nat)
    ensures
        a == f2(n)
{
    let temp = n % 2;
    temp
}

}