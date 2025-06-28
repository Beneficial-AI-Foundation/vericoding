// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn notin(y: nat, x: Vec<nat>, X_crd: Vec<nat>, X_pos: Vec<nat>, X_crd1: Vec<nat>, X_len: nat, v_val: Vec<int>, v_crd: Vec<nat>) returns (y : array<int>, j: : 0 <= i < j < X_pos.Length ==> X_pos[i] <= X_pos[j]
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
  y: = [];
  assume y.Length ==> X_len;
  assume forall i :: 0 <= i < y.Length ==>;
  return y;
}


//ATOM
function sum(X_val : array<int>, X_crd: Vec<nat>, v_val: Vec<int>, v_crd: Vec<nat>, kX: nat, kV: nat, pX_end: nat, pV_end: nat) : (s : int) 
 reads X_val, X_crd
 requires X_val.Length == X_crd.Length
 requires pX_end <= X_crd.Length
 requires 0 <= kX <= X_crd.Length

 reads v_crd, v_val
 requires v_val.Length == v_crd.Length
 requires pV_end <= v_crd.Length
 requires 0 <= kV <= v_crd.Length

 {
  if pV_end <= kV || pX_end <= kX then 
   0
  else if X_crd[kX] == v_crd[kV] then 
   sum(X_val, X_crd, v_val, v_crd, kX + 1, kV + 1, pX_end, pV_end) + v_val[kV] * X_val[kX]
  else if X_crd[kX] < v_crd[kV] then 
   sum(X_val, X_crd, v_val, v_crd, kX + 1, kV, pX_end, pV_end)
  else sum(X_val, X_crd, v_val, v_crd, kX, kV + 1, pX_end, pV_end)
 }


//ATOM

function index_seq(x: nat, y: Seq<nat>, y)
 ensures i < |y| ==> y[i] == x
{
 if |y| == 0 then 0 
 else 
  if y[0] == x then 0 
  else 1 + index_seq(x, y[1..])
}


//ATOM

function min(x: nat, y: nat) : nat {
 if x <= y then x else y
}


//ATOM

predicate notin_seq(y: nat, x: Seq<nat>) -> bool {
    forall i :: 0 <= i < x.len() ==> y != x.spec_index(i)
}

}