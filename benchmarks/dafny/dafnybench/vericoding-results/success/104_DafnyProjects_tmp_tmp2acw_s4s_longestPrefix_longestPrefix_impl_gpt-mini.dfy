// MFES, Exam 8/Sept/20201, Exercise 5 

// Computes the length (i) of the longest common prefix (initial subarray) 
// of two arrays a and b.

// <vc-helpers>
lemma ExtendPrefix(a: array<int>, b: array<int>, i: nat)
  requires i < a.Length && i < b.Length
  requires a[..i] == b[..i]
  requires a[i] == b[i]
  ensures a[..i+1] == b[..i+1]
{
  calc {
    a[..i+1];
    == { } a[..i] + [a[i]];
    == { assert a[..i] == b[..i]; } b[..i] + [a[i]];
    == { assert a[i] == b[i]; } b[..i] + [b[i]];
    == { } b[..i+1];
  }
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
    invariant 0 <= i <= a.Length
    invariant i <= b.Length
    invariant a[..i] == b[..i]
    decreases a.Length - i
  {
    i := i + 1;
  }
}
// </vc-code>

// Test method with an example.