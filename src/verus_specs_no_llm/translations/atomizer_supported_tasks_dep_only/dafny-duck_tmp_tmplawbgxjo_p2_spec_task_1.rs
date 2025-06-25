// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn absx(x: Vec<int>) -> (y: Vec<int>)
    ensures y.len() == x.len(),
            forall|i: int| 0 <= i < y.len() ==>  y[i] == abs(x[i])
{
}

}