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

spec fn notin(y: nat, x: Vec<nat>, X_crd: Vec<nat>, v_val: Vec<int>, v_crd: Vec<nat>, kX: nat, kV: nat, pX_end: nat, pV_end: nat) : (s : int) 
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