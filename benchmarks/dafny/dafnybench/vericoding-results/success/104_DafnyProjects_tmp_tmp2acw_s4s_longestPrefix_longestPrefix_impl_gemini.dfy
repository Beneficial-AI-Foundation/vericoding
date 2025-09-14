// <vc-preamble>
// </vc-preamble>

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
  i := 0;
  while i < a.Length && i < b.Length && a[i] == b[i]
    invariant 0 <= i <= a.Length
    invariant 0 <= i <= b.Length
    invariant a[..i] == b[..i]
  {
    i := i + 1;
  }
}
// </vc-code>
