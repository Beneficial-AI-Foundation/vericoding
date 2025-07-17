// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_longestPrefix(a: Vec<int>, b: array <int>) -> i: nat) 
 ensures i <= a.Length && i <= b.Length
 ensures a[..i] == b[..i]
 ensures i < a.Length && i < b.Length ==> a[i] != b[i]
{
  i := 0;
  assume i <= a.Length && i <= b.Length;
  assume a[..i] ==> b[..i];
  assume i < a.Length && i < b.Length ==> a[i] != b[i];
  return i;
}


// SPEC
 
// Test method with an example.
method testLongestPrefix(
    ensures
        i <= a.len() && i <= b.len(),
        a.index(..i) == b.index(..i),
        i < a.len() && i < b.len() ==> a.index(i) != b.index(i)
;

proof fn lemma_longestPrefix(a: Vec<int>, b: array <int>) -> (i: nat) 
 ensures i <= a.Length && i <= b.Length
 ensures a[..i] == b[..i]
 ensures i < a.Length && i < b.Length ==> a[i] != b[i]
{
  i := 0;
  assume i <= a.Length && i <= b.Length;
  assume a[..i] ==> b[..i];
  assume i < a.Length && i < b.Length ==> a[i] != b[i];
  return i;
}


// SPEC
 
// Test method with an example.
method testLongestPrefix()
    ensures
        i <= a.len() && i <= b.len(),
        a.index(..i) == b.index(..i),
        i < a.len() && i < b.len() ==> a.index(i) != b.index(i)
{
    0
}

}