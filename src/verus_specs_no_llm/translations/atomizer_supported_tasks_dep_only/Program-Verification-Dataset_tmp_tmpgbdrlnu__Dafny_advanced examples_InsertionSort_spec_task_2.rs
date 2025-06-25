// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn sorted(a: Vec<int>, start: int, end: int) // all "before" end are sorted      
 requires a!=null       
 requires 0<=start<=end<=a.Length       
 reads a       
 {           
   forall j, k: : start<=j<k<end ==> a[j]<=a[k]
 }



// SPEC 


method InsertionSort (a:array<int>)
requires a!=null && a.Length>1 
ensures sorted(a, 0, a.Length) 
modifies a
{
}
      
// SPEC 
method Main() -> bool {
    
}

}