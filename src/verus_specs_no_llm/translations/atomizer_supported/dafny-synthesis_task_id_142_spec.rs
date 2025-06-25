// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn CountIdenticalPositions(a: Seq<int>, b: Seq<int>, c: Seq<int>) -> (count: int)
    requires a.len() == b.len() and b.len() == c.len()
    ensures count >= 0,
            count ==  set i: int .len() 0 <= i < a.len() and a[i] == b[i] and b[i] == c[i]|
{
}

}