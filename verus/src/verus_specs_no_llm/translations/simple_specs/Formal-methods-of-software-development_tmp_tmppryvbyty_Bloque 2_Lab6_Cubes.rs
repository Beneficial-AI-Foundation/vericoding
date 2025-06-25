// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn main() {
}

fn Cubes(n: int) -> (s: Seq<int>)
    requires
        n >= 0
    ensures
        s.len() == n,
        forall i:int :: 0 <= i < n ==> s.spec_index(i) == i*i*i
{
    return Seq::empty();
}

}