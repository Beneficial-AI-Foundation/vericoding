// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn mroot2(n: int) -> (r: int) //Cost O(n)
    requires
        n>=0
    ensures
        r>=0 && r*r <= n <(r+1)*(r+1)
{
    return 0;
}

}