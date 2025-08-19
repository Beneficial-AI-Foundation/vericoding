//IMPL 
method IsGreater(n: int, a: array<int>) returns (result: bool)
  /* code modified by LLM (iteration 1): removed redundant null check since array<int> is non-null by default */
  ensures result ==> forall i :: 0 <= i < a.Length ==> n > a[i]
  ensures !result ==> exists i :: 0 <= i < a.Length && n <= a[i]
{
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> n > a[j]
  {
    if n <= a[i] {
      result := false;
      return;
    }
    i := i + 1;
  }
  result := true;
}