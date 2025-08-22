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


//IMPL unique
method unique(a: seq<int>) returns (b: seq<int>) 
  requires sorted(a)
  ensures true
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
    invariant b[0] == a[0]
    invariant forall j :: 0 <= j < |b| - 1 ==> b[j] < b[j+1]
    invariant forall j :: 0 <= j < i ==> exists k :: 0 <= k < |b| && b[k] == a[j]
    invariant forall k :: 0 <= k < |b| ==> exists j :: 0 <= j < i && b[k] == a[j]
  {
    if a[i] != b[|b| - 1] {
      b := b + [a[i]];
    }
    i := i + 1;
  }
}

/**
 * Dafny compiles the Main method if it finds one in a file.
 */