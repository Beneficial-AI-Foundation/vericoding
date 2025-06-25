// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn positive(s: Seq<int>) -> bool {
    forall u::0<=u<s.len() ==> s.spec_index(u)>=0
}

fn mcountEven(v: Vec<int>) -> (n: int)
    requires
        positive(v.spec_index(..))
    ensures
        n==CountEven(v.spec_index(..))
{
    return 0;
}

}