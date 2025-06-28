// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn CountIdenticalPositions(a: Seq<int>, b: Seq<int>, c: Seq<int>) -> (count: int)
    requires
        a.len() == b.len() && b.len() == c.len()
    ensures
        count >= 0,
        count ==  set i: int .len() 0 <= i < a.len() && a.spec_index(i) == b.spec_index(i) && b.spec_index(i) == c.spec_index(i)|
{
    return 0;
}

}