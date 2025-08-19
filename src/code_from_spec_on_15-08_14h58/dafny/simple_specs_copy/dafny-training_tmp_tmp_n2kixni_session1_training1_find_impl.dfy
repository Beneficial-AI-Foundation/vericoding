// IMPL
method find(a: seq<int>, key: int) returns (index: int)
  requires true
  ensures true
{
  index := -1;
  var i := 0;
  while i < |a|
  {
    if a[i] == key {
      index := i;
      return;
    }
    i := i + 1;
  }
}

// Prove more complicated invariants with quantifiers.

/**
 * Palindrome checker.
 * Example 3.
 *
 * Check whether a sequence of letters is a palindrome.
 *
 * Try to:
 * 1. write the algorithm to determine whether a string is a palindrome
 * 2. write the ensures clauses that specify the palidrome properties
 * 3. verify algorithm. 
 *
 * Notes: a[k] accesses element k of a for 0 <= k < |a|
 * a[i..j] is (a seq) with the first j elements minus the first i
 * a[0..|a|] is same as a. 
 */