// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn notin(y: nat, x: Vec<nat>, x: Seq<nat>) -> bool {
    forall i :: 0 <= i < x.len() ==> y != x.spec_index(i)
}

fn DSpMSpV(X_val: Vec<int>, X_crd: Vec<nat>, X_pos: Vec<nat>, X_crd1: Vec<nat>, X_len: nat, v_val: Vec<int>, v_crd: Vec<nat>) -> (y: Vec<int>, j: : 0 <= i < j < X_pos.Length ==> X_pos[i] <= X_pos[j];
  requires forall i :: 0 <= i < X_pos.Length ==> 0 <= X_pos[i] <= X_val.Length

  requires X_len >= X_crd1.Length
  requires forall i :: 0 <= i < X_crd1.Length ==> X_crd1[i] < X_len

  requires X_crd1.Length < X_pos.Length
  requires forall i, j: : 0 <= i < j < X_crd1.Length ==> X_crd1[i] < X_crd1[j]

  // v requirements 
  requires v_val.Length == v_crd.Length

  ensures y.Length == X_len
  ensures forall i :: 0 <= i < y.Length ==> 
    y[i] == 
      if index(i, X_crd1) < X_crd1.Length then 
        sum(X_val, X_crd, v_val, v_crd, X_pos[index(i, X_crd1)], 0, X_pos[index(i, X_crd1)+1], v_val.Length)
      else 0
  {
}


// SPEC 

method Main()
    requires
        X_pos.len() >= 1,
        X_val.len() == X_crd.len(),
        forall i, j :: 0 <= i < j < X_pos.len() ==> X_pos.spec_index(i) <= X_pos.spec_index(j),
        forall i :: 0 <= i < X_pos.len() ==> 0 <= X_pos.spec_index(i) <= X_val.len(),
        X_len >= X_crd1.len(),
        forall i :: 0 <= i < X_crd1.len() ==> X_crd1.spec_index(i) < X_len,
        X_crd1.len() < X_pos.len(),
        forall i, j :: 0 <= i < j < X_crd1.len() ==> X_crd1.spec_index(i) < X_crd1.spec_index(j)

  // v requirements,
        v_val.len() == v_crd.len()
    ensures
        y.len() == X_len,
        forall i :: 0 <= i < y.len() ==> 
    y.spec_index(i) == 
      if index(i, X_crd1) < X_crd1.len() then 
        sum(X_val, X_crd, v_val, v_crd, X_pos.spec_index(index(i, X_crd1)), 0, X_pos.spec_index(index(i, X_crd1)+1), v_val.len())
      else 0
{
    return Vec::new();
}

}