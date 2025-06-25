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

spec fn sorted(a: array?<int>, l: int, u: int)
  reads a;
  requires a != null;
  {
    forall i, j: : 0 <= l <= i <= j <= u < a.Length ==> a[i] <= a[j]
  }

// ATOM 
predicate partitioned(a: array?<int>, i: int)
  reads a
  requires a != null
  {
    forall k, k': : 0 <= k <= i < k' < a.Length ==> a[k] <= a[k']
  }


// SPEC 

method BubbleSort(a: array?<int>)
  modifies a
  requires a != null
  {
}

  
// SPEC 
  
method Main() -> bool {
    
}

}