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

fn MinSecondValueFirst(s: Vec<Seq<int>>) -> (firstOfMinSecond: int)
    requires
        s.len() > 0,
        forall i :: 0 <= i < s.len() ==> s.spec_index(i).len() >= 2
    ensures
        exists i :: 0 <= i < s.len() && firstOfMinSecond == s.spec_index(i)[0] && 
    (forall j :: 0 <= j < s.len() ==> s.spec_index(i)[1] <= s.spec_index(j)[1])
{
    return 0;
}

}