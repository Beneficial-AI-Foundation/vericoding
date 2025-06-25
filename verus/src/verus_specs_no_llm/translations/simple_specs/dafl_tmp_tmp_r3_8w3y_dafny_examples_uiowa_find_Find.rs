// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Find(a: Vec<int>, key: int) -> (i: int)
    requires
        a != null
  // if i is non-negative then
    ensures
        0 <= i ==> (// (1) i is smaller than the length of a
            i < a.len() && 
            // (2) key is at position i in a
            a.spec_index(i) == key && 
            // (3) i is the smallest position where key appears
            forall k :: 0 <= k < i ==> a.spec_index(k) != key
           ),
        i < 0 ==> 
      // a does not contain key
      forall k :: 0 <= k < a.len() ==> a.spec_index(k) != key
{
    return 0;
}

}