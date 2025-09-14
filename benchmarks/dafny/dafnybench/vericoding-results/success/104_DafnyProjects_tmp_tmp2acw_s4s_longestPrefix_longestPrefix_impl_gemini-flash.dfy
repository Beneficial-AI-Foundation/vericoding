// MFES, Exam 8/Sept/20201, Exercise 5 

// Computes the length (i) of the longest common prefix (initial subarray) 
// of two arrays a and b.

// <vc-helpers>
lemma lemma_equal_prefix(a: array<int>, b: array<int>, k: nat)
  requires k <= a.Length && k <= b.Length
  requires forall j :: 0 <= j < k ==> a[j] == b[j]
  ensures a[..k] == b[..k]
{}

lemma lemma_a_not_eq_b(a: array<int>, b: array<int>, k: nat)
  requires k < a.Length && k < b.Length
  requires a[k] != b[k]
  ensures exists j :: 0 <= j < k+1 && a[j] != b[j]
{}
// </vc-helpers>

// <vc-spec>
method longestPrefix(a: array<int>, b: array <int>) returns (i: nat) 
 ensures i <= a.Length && i <= b.Length
 ensures a[..i] == b[..i]
 ensures i < a.Length && i < b.Length ==> a[i] != b[i]
// </vc-spec>
// <vc-code>
{
  var commonLength := 0;
  while commonLength < a.Length && commonLength < b.Length
    invariant 0 <= commonLength <= a.Length
    invariant 0 <= commonLength <= b.Length
    invariant forall j :: 0 <= j < commonLength ==> a[j] == b[j]
  {
    if a[commonLength] == b[commonLength] {
      commonLength := commonLength + 1;
    } else {
      break;
    }
  }
  i := commonLength; // Assign the value to the result variable 'i'
  assert forall j :: 0 <= j < i ==> a[j] == b[j];
  lemma_equal_prefix(a, b, i);
  if i < a.Length && i < b.Length {
    assert a[i] != b[i];
  }
}
// </vc-code>

// Test method with an example.