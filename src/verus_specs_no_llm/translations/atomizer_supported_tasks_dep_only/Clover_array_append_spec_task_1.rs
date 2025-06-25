// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn append(a: Vec<int>, b: int) -> (c: Vec<int>)
    ensures a[..] + [b] == c[..]
{
}

}