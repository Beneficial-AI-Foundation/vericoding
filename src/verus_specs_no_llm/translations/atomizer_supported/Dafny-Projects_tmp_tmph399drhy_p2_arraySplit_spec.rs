// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn ArraySplit(a: Vec<int>) -> b: Vec<int>, c: Vec<int>
    ensures fresh(b),
            fresh(c),
            a[..] == b[..] + c[..],
            a.len() == b.len() + c.len(),
            a.len() > 1 ==> a.len() > b.len(),
            a.len() > 1 ==> a.len() > c.len()
{
}

}