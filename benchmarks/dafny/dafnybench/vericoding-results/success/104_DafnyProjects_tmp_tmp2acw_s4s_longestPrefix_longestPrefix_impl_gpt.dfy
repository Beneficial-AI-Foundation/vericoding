// MFES, Exam 8/Sept/20201, Exercise 5 

// Computes the length (i) of the longest common prefix (initial subarray) 
// of two arrays a and b.

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method longestPrefix(a: array<int>, b: array <int>) returns (i: nat) 
 ensures i <= a.Length && i <= b.Length
 ensures a[..i] == b[..i]
 ensures i < a.Length && i < b.Length ==> a[i] != b[i]
// </vc-spec>
// <vc-code>
{
  var n := a.Length;
  var m := b.Length;
  i := 0;
  while i < n && i < m && a[i] == b[i]
    invariant 0 <= i <= n
    invariant 0 <= i <= m
    invariant a[..i] == b[..i]
    decreases n - i
  {
    var oldI := i;
    i := i + 1;
    assert oldI < n && oldI < m;
    assert a[..i] == a[..oldI] + [a[oldI]];
    assert b[..i] == b[..oldI] + [b[oldI]];
    assert a[..oldI] + [a[oldI]] == b[..oldI] + [b[oldI]];
  }
}
// </vc-code>

// Test method with an example.