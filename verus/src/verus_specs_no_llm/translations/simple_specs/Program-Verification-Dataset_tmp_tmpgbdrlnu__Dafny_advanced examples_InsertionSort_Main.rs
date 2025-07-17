// Translated from Dafny
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
    var a := new int.index(5);
 a.index(0),a.index(1),a.index(2),a.index(3),a.index(4) := 3,2,5,1,8;
 InsertionSort(a);
 print a.index(..)
}

}