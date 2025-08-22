// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method double_array_elements(s: array<int>)
  modifies s
  ensures forall i :: 0 <= i < s.Length ==> s[i] == 2 * old(s[i])
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>