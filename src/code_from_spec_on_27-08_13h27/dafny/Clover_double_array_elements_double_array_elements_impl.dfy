// <vc-helpers>
// No additional helpers or proofs needed for this implementation
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method double_array_elements(s: array<int>)
  modifies s
  ensures forall i :: 0 <= i < s.Length ==> s[i] == 2 * old(s[i])
// </vc-spec>
// </vc-spec>

// <vc-code>
method double_array_elements_impl(s: array<int>)
  modifies s
  ensures forall i :: 0 <= i < s.Length ==> s[i] == 2 * old(s[i])
{
  for i := 0 to s.Length
    invariant forall k :: 0 <= k < i ==> s[k] == 2 * old(s[k])
    invariant forall k :: i <= k < s.Length ==> s[k] == old(s[k])
  {
    s[i] := 2 * s[i];
  }
}
// </vc-code>
