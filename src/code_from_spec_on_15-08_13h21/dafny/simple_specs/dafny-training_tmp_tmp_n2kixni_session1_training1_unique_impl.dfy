//ATOM
predicate sorted(a: seq<int>) 
{
  forall j, k::0 <= j < k < |a| ==> a[j] <= a[k]
}

/**
 * Example 4.
 *
 * Remove duplicates from a sorted sequence.
 *
 * Try to:
 * 1. write the code to compute b
 * 2. write the ensures clauses that specify the remove duplicates properties
 * 3. verify algorithm. 
 *
 * Notes: a[k] accesses element k of a for 0 <= k < |a|
 * a[i..j] is (a seq) with the first j elements minus the first i
 * a[0.. |a| - 1] is same as a. 
 */

//IMPL
method unique(a: seq<int>) returns (b: seq<int>) 
  requires sorted(a)
  ensures sorted(b)
  ensures forall x :: x in b ==> x in a
  ensures forall x :: x in a ==> x in b
  ensures forall i, j :: 0 <= i < j < |b| ==> b[i] < b[j]
{
  if |a| == 0 {
    b := [];
    return;
  }
  
  b := [a[0]];
  var i := 1;
  
  while i < |a|
    invariant 1 <= i <= |a|
    invariant |b| >= 1
    invariant sorted(b)
    invariant forall x :: x in b ==> x in a[0..i]
    invariant forall x :: x in a[0..i] ==> x in b
    invariant forall j, k :: 0 <= j < k < |b| ==> b[j] < b[k]
    invariant b[|b|-1] == a[i-1]
  {
    if a[i] != a[i-1] {
      b := b + [a[i]];
    }
    i := i + 1;
  }
}

/**
 * Dafny compiles the Main method if it finds one in a file.
 */