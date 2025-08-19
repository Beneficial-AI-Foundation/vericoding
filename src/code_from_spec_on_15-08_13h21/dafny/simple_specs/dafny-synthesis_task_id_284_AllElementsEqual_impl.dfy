method AllElementsEqual(a: array<int>, n: int) returns (result: bool)
  /* code modified by LLM (iteration 1): removed unnecessary null check since array<int> is non-null type */
  ensures result ==> forall i :: 0 <= i < a.Length ==> a[i] == n
  ensures !result ==> exists i :: 0 <= i < a.Length && a[i] != n
{
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> a[j] == n
  {
    if a[i] != n {
      result := false;
      return;
    }
    i := i + 1;
  }
  result := true;
}