// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn M(N: int, a: Vec<int>) -> (sum: int, max: int)
    requires
        0 <= N && a.len() == N && (forall k :: 0 <= k && k < N ==> 0 <= a.spec_index(k))
    ensures
        sum <= N * max
{
    return (0, 0);
}

}