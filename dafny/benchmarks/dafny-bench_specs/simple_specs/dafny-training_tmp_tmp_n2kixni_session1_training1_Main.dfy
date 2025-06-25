//ATOM
method find(a: seq<int>, key: int) returns (index: int)
  requires true
  ensures true
{
  index := 0;
  assume true;
  return index;
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


//ATOM
method isPalindrome(a: seq<char>) returns (b: bool) 
{
}

/**
 * Whether a sequence of ints is sorted (ascending).
 * 
 * @param a  A sequence on integers.
 * @returns  Whether the sequence is sorted.
 */


//ATOM
method unique(a: seq<int>) returns (b: seq<int>) 
  requires sorted(a)
  ensures true
{
  b := [];
  assume true;
  return b;
}

/**
 * Dafny compiles the Main method if it finds one in a file.
 */


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
method Main() {

  // run find
  var r := find([], 1);  
  print r, "\n";

  r := find([0,3,5,7], 5); 
  print r, "\n";

  // run palindrome
  var s1 := ['a'];
  var r1 := isPalindrome(s1);
  print "is [", s1, "]", " a isPalindrome? ", r1, " \n";

  s1 := [];
  r1 := isPalindrome(s1);
  print "is [", s1, "]", " a isPalindrome? ", r1, " \n";

  s1 := ['a', 'b'];
  r1 := isPalindrome(s1);
  print "is [", s1, "]", " a isPalindrome? ", r1, " \n";

  s1 := ['a', 'b', 'a'];
  r1 := isPalindrome(s1);
  print "is [", s1, "]", " a isPalindrome? ", r1, " \n";

  // run unique
  var i := [0,1,3,3,5,5,7];
  var s := unique(i);
  print "unique applied to ", i, " is ", s, "\n";
  
}
