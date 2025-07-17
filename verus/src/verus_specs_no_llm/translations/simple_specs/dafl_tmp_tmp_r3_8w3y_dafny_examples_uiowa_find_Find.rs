// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_Find(a: Vec<int>, key: int) -> i: int
    requires
        a != null
  // if i is non-negative then
    ensures
        0 <= i ==> (// (1) i is smaller than the length of a
            i < a.len() && 
            // (2) key is at position i in a
            a.index(i) == key && 
            // (3) i is the smallest position where key appears
            forall |k: int| 0 <= k < i ==> a.index(k) != key
           ),
        i < 0 ==> 
      // a does not contain key
      forall |k: int| 0 <= k < a.len() ==> a.index(k) != key
;

proof fn lemma_Find(a: Vec<int>, key: int) -> (i: int)
    requires
        a != null
  // if i is non-negative then
    ensures
        0 <= i ==> (// (1) i is smaller than the length of a
            i < a.len() && 
            // (2) key is at position i in a
            a.index(i) == key && 
            // (3) i is the smallest position where key appears
            forall |k: int| 0 <= k < i ==> a.index(k) != key
           ),
        i < 0 ==> 
      // a does not contain key
      forall |k: int| 0 <= k < a.len() ==> a.index(k) != key
{
    0
}

}