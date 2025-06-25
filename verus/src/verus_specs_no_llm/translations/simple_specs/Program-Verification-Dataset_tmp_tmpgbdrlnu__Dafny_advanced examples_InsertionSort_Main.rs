// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sorted(a: Vec<int>, start: int, end: int) // all "before" end are sorted   
 requires a!=null    
 requires 0<=start<=end<=a.Length    
 reads a    
 {      
  forall j, k: : start<=j<k<end ==> a[j]<=a[k]
 }


// SPEC
method Main() -> bool {
    var a := new int.spec_index(5);
 a.spec_index(0),a.spec_index(1),a.spec_index(2),a.spec_index(3),a.spec_index(4) := 3,2,5,1,8;
 InsertionSort(a);
 print a.spec_index(..)
}

}