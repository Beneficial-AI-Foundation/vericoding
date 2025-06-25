// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn isSorted(a: Vec<int>, from: nat, to: nat)
  reads a
  requires 0 <= from <= to <= a.Length
{
    forall i, j: : from <= i < j < to ==> a[i] <= a[j]
}


// Simple test case to check the postcondition
// SPEC 

// Simple test case to check the postcondition
method testInsertionSort() -> bool {
    
}

}