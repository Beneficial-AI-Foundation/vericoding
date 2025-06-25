// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn remove_front(a: Vec<int>) -> (c: Vec<int>)
    requires a.len()>0
    ensures a[1..] == c[..]
{
}

}