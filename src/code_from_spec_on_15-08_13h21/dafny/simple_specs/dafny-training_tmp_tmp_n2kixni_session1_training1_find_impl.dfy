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

predicate isPalindrome(s: seq<char>)
{
  forall i :: 0 <= i < |s| ==> s[i] == s[|s| - 1 - i]
}

method checkPalindrome(s: seq<char>) returns (result: bool)
  ensures result <==> isPalindrome(s)
  ensures result <==> (forall i :: 0 <= i < |s| ==> s[i] == s[|s| - 1 - i])
{
  if |s| <= 1 {
    return true;
  }
  
  var left := 0;
  var right := |s| - 1;
  
  /* code modified by LLM (iteration 1): Fixed loop invariants and added relationship between left, right and palindrome indices */
  while left < right
    invariant 0 <= left <= |s|
    invariant 0 <= right < |s|
    invariant left + right == |s| - 1
    invariant left <= right + 1
    invariant forall i :: 0 <= i < left ==> s[i] == s[|s| - 1 - i]
    invariant forall i :: right < i < |s| ==> s[i] == s[|s| - 1 - i]
  {
    if s[left] != s[right] {
      /* code modified by LLM (iteration 1): Used the invariant relationship to prove the assertion */
      assert left + right == |s| - 1;
      assert right == |s| - 1 - left;
      assert s[left] != s[|s| - 1 - left];
      return false;
    }
    /* code modified by LLM (iteration 1): Added assertions to help maintain loop invariants */
    assert s[left] == s[right];
    assert s[left] == s[|s| - 1 - left];
    left := left + 1;
    right := right - 1;
  }
  
  /* code modified by LLM (iteration 1): Added assertion to help prove postcondition when returning true */
  assert left >= right;
  assert forall i :: 0 <= i < |s| ==> s[i] == s[|s| - 1 - i];
  return true;
}