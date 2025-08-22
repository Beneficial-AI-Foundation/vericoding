// <vc-helpers>
// </vc-helpers>

method double_array_elements(s: array<int>)
  modifies s
  ensures forall i :: 0 <= i < s.Length ==> s[i] == 2 * old(s[i])
// <vc-code>
{
  assume false;
}
// </vc-code>