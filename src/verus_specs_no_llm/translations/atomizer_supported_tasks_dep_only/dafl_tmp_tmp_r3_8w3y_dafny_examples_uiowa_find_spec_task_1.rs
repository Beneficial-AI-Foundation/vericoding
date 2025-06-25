// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn Find(a: Vec<int>, key: int) -> (i: int)
    requires a != null;
   // if i is non-negative then
    ensures 0 <= i ==> (// (1) i is smaller than the length of a
                       i < a.len() and 
                       // (2) key is at position i in a
                       a[i] == key and 
                       // (3) i is the smallest position where key appears
                       forall|k: int| 0 <= k < i ==> a[k] != key
                      );
   // if index is negative then,
            i < 0 ==> 
           // a does not contain key
           forall|k: int| 0 <= k < a.len() ==> a[k] != key;
{
}

}