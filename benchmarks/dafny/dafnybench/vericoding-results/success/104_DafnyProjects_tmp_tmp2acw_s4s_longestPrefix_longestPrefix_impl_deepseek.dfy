// MFES, Exam 8/Sept/20201, Exercise 5 

// Computes the length (i) of the longest common prefix (initial subarray) 
// of two arrays a and b.

// <vc-helpers>
lemma CommonPrefixLemma(a: array<int>, b: array<int>, i: nat)
  requires i <= a.Length && i <= b.Length
  requires forall j :: 0 <= j < i ==> a[j] == b[j]
  ensures a[..i] == b[..i]
{
}
// </vc-helpers>

// <vc-spec>
method longestPrefix(a: array<int>, b: array <int>) returns (i: nat) 
 ensures i <= a.Length && i <= b.Length
 ensures a[..i] == b[..i]
 ensures i < a.Length && i < b.Length ==> a[i] != b[i]
// </vc-spec>
// <vc-code>
{
  i := 0;
  while i < a.Length && i < b.Length && a[i] == b[i]
    invariant 0 <= i <= a.Length && i <= b.Length
    invariant forall j :: 0 <= j < i ==> a[j] == b[j]
  {
    i := i + 1;
  }
}
// </vc-code>

// Test method with an example.