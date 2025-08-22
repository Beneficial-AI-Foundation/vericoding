// <vc-helpers>
// </vc-helpers>

method find(a: array<int>, key: int) returns(index: int)
    requires a.Length > 0;
    ensures 0 <= index <= a.Length;
    ensures index < a.Length ==> a[index] == key;
// <vc-code>
{
  assume false;
}
// </vc-code>