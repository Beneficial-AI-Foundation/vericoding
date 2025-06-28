use builtin::*;
use builtin_macros::*;

verus! {

spec fn f2(n: nat) -> nat {
    (n % 2) as nat
}

fn main() {
}

fn mod2(n: nat) -> (a: nat)
    ensures
        a == f2(n)
{
    let temp = n % 2;
    assert(temp >= 0); // Prove that n % 2 is non-negative
    assert(temp == 0 || temp == 1); // Prove that n % 2 is either 0 or 1
    let result = temp as nat;
    assert(result == f2(n)); // Prove the postcondition
    result
}

}