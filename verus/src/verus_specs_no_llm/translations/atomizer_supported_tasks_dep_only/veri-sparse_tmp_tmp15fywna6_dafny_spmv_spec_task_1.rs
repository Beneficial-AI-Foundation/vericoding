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

fn SpMV(X_val: Vec<int>, X_crd: Vec<nat>, X_pos: Vec<nat>, v: Vec<int>) -> (y: Vec<int>)
    requires
        X_crd.len() >= 1,
        X_crd.len() == X_val.len(),
        forall i, j :: 0 <= i < j < X_pos.len() ==> X_pos.spec_index(i) <= X_pos.spec_index(j),
        forall i :: 0 <= i < X_crd.len() ==> X_crd.spec_index(i) < v.len(),
        forall i :: 0 <= i < X_pos.len() ==> X_pos.spec_index(i) <= X_val.len(),
        X_pos.len() >= 1
    ensures
        y.len() + 1 == X_pos.len(),
        forall i :: 0 <= i < y.len() ==> y.spec_index(i) == sum(X_val, X_crd, v, X_pos.spec_index(i), X_pos.spec_index(i + 1))
{
    return Vec::new();
}

}