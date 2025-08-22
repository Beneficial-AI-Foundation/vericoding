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


// SPEC
method unique(a: seq<int>) returns (b: seq<int>) 
  requires sorted(a)
  ensures true
{
}

/**
 * Dafny compiles the Main method if it finds one in a file.
 */
