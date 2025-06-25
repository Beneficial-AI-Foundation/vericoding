// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn single(x: Vec<int>, y: Vec<int>) -> (b: Vec<int>)
    requires x.len() > 0,
             y.len() > 0
// ensuring that the new array is the two arrays joined
    ensures b[..] == x[..] + y[..]
{
}

}