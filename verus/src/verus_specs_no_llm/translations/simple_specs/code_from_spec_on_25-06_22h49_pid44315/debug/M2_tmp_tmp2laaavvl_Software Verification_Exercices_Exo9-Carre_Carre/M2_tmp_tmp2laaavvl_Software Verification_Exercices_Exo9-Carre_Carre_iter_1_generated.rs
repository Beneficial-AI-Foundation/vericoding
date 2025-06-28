use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Carre(a: nat) -> (c: nat)
    ensures
        c == a*a
{
    return a * a;
}

}

The implementation satisfies the postcondition `c == a*a` by directly computing and returning `a * a`. Since both `a` and the result of `a * a` are natural numbers (non-negative integers), this implementation is correct and should verify successfully in Verus.