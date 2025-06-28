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
    let result = (n % 2) as nat;
    assert(n % 2 >= 0); // This is automatically true since n >= 0 and modulo preserves sign
    result
}

}