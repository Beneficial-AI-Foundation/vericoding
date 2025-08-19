method HasCommonElement(a: array<int>, b: array<int>) returns (result: bool)
  /* code modified by LLM (iteration 1): removed null checks since arrays are non-null by default in Dafny */
  ensures result ==> exists i, j :: 0 <= i < a.Length && 0 <= j < b.Length && a[i] == b[j]
  ensures !result ==> forall i, j :: 0 <= i < a.Length && 0 <= j < b.Length ==> a[i] != b[j]
{
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall x, y :: 0 <= x < i && 0 <= y < b.Length ==> a[x] != b[y]
  {
    var j := 0;
    while j < b.Length
      invariant 0 <= j <= b.Length
      invariant forall y :: 0 <= y < j ==> a[i] != b[y]
    {
      if a[i] == b[j] {
        result := true;
        return;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  result := false;
}