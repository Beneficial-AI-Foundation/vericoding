// ex3errors.dfy in Assignment 1
// verify that an array of characters is a Palindrome
/*
A Palindrome is a word that is the same when written forwards and when written backwards. 
For example, the word ”refer” is a Palindrome.
The method PalVerify is supposed to verify whether a word is a Palindrome, 
where the word is represented as an array of characters. 
The method was written by a novice software engineer, and contains many errors.

   i) Without changing the signature or the code in the while loop, 
      fix the method so that it veriifes the code. Do not add any Dafny predicates or functions: 
      keep the changes to a minimum.

   ii) Write a tester method (you may call it anything you like) that verifies that the 
      testcases refer, z and the empty string are Palindromes, and xy and 123421 are not. 
      The tester should not generate any output.
*/

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method PalVerify(a: array<char>) returns (yn: bool)
ensures yn == true ==> forall i :: 0 <= i < a.Length/2 ==> a[i] == a[a.Length - i -1]
ensures yn == false ==> exists i :: 0 <= i < a.Length/2 && a[i] != a[a.Length - i -1]
ensures forall j :: 0<=j<a.Length ==> a[j] == old(a[j])
// </vc-spec>
// <vc-code>
{
  var i := 0;
  yn := true;
  while i < a.Length / 2
    invariant 0 <= i <= a.Length / 2
    invariant forall k :: 0 <= k < i ==> a[k] == a[a.Length - k - 1]
    decreases a.Length / 2 - i
  {
    // Access bounds for a[i] and its mirror are justified by the loop condition and invariants
    if a[i] != a[a.Length - i - 1] {
      yn := false;
      assert 0 <= i && i < a.Length / 2;
      assert a[i] != a[a.Length - i - 1];
      assert exists j :: 0 <= j < a.Length / 2 && a[j] != a[a.Length - j - 1];
      return;
    }
    i := i + 1;
  }
  yn := true;
}
// </vc-code>

