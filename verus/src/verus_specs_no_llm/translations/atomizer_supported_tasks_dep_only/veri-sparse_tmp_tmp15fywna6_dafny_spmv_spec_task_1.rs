// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sum(X_val: Vec<int>, X_crd: Vec<nat>, v: Vec<int>, b: int, k: int) -> (s : int)
  reads X_val, X_crd, v
    requires
        X_val.len() >= b >= 0,
        k <= X_val.len(),
        X_val.len() == X_crd.len(),
        forall |i: int| 0 <= i < X_crd.len() ==> 0 <= X_crd.index(i) < v.len()
{
    (0, 0, 0)
}

spec fn spec_SpMV(X_val: Vec<int>, X_crd: Vec<nat>, X_pos: Vec<nat>, v: Vec<int>) -> y : array<int>
    requires
        X_crd.len() >= 1,
        X_crd.len() == X_val.len(),
        forall |i: int, j: int| 0 <= i < j < X_pos.len() ==> X_pos.index(i) <= X_pos.index(j),
        forall |i: int| 0 <= i < X_crd.len() ==> X_crd.index(i) < v.len(),
        forall |i: int| 0 <= i < X_pos.len() ==> X_pos.index(i) <= X_val.len(),
        X_pos.len() >= 1
    ensures
        y.len() + 1 == X_pos.len(),
        forall |i: int| 0 <= i < y.len() ==> y.index(i) == sum(X_val, X_crd, v, X_pos.index(i), X_pos.index(i + 1))
;

proof fn lemma_SpMV(X_val: Vec<int>, X_crd: Vec<nat>, X_pos: Vec<nat>, v: Vec<int>) -> (y: Vec<int>)
    requires
        X_crd.len() >= 1,
        X_crd.len() == X_val.len(),
        forall |i: int, j: int| 0 <= i < j < X_pos.len() ==> X_pos.index(i) <= X_pos.index(j),
        forall |i: int| 0 <= i < X_crd.len() ==> X_crd.index(i) < v.len(),
        forall |i: int| 0 <= i < X_pos.len() ==> X_pos.index(i) <= X_val.len(),
        X_pos.len() >= 1
    ensures
        y.len() + 1 == X_pos.len(),
        forall |i: int| 0 <= i < y.len() ==> y.index(i) == sum(X_val, X_crd, v, X_pos.index(i), X_pos.index(i + 1))
{
    Vec::new()
}

}