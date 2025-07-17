// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn notin(y: nat, x: Vec<nat>, x: Seq<nat>) -> bool {
    forall |i: int| 0 <= i < x.len() ==> y != x.index(i)
}

spec fn sum(X_val: Vec<int>, X_crd: Vec<nat>, v_val: Vec<int>, v_crd: Vec<nat>, kX: nat, kV: nat, pX_end: nat, pV_end: nat) -> (s : int) 
  reads X_val, X_crd
    requires
        X_val.len() == X_crd.len(),
        pX_end <= X_crd.len(),
        0 <= kX <= X_crd.len()

  reads v_crd, v_val,
        v_val.len() == v_crd.len(),
        pV_end <= v_crd.len(),
        0 <= kV <= v_crd.len()
{
    (0, 0)
}

}