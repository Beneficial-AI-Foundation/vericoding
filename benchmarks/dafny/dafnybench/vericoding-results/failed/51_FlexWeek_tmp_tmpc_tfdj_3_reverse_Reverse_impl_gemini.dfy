// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Reverse(a: array<char>) returns (b: array<char>)
requires a.Length > 0
ensures a.Length == b.Length
ensures forall k :: 0 <= k < a.Length ==> b[k] == a[(a.Length-1) - k];
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Corrected the for loop range to iterate over all elements. */
  b := new char[a.Length];
  for i := 0 to a.Length
    invariant b.Length == a.Length
    invariant forall k :: 0 <= k < i ==> b[k] == a[(a.Length-1) - k]
  {
    b[i] := a[(a.Length - 1) - i];
  }
}
// </vc-code>
