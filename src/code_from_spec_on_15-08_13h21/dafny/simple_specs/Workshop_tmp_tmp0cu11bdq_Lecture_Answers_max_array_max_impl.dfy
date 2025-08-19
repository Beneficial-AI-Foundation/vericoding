method max(a:array<int>) returns(max:int)
  /* code modified by LLM (iteration 1): removed unnecessary null check since array<int> is non-nullable */
  ensures forall j :: j >= 0 && j < a.Length ==> max >= a[j] //max is larger then anything in the array
  /* code modified by LLM (iteration 1): removed deprecated semicolon from ensures clause */
  ensures a.Length > 0 ==> exists j :: j >= 0 && j < a.Length && max == a[j] //max is an element in the array
  /* code modified by LLM (iteration 1): removed deprecated semicolon from ensures clause */
{
  if a.Length == 0 {
    max := 0;
  } else {
    max := a[0];
    var i := 1;
    while i < a.Length
      invariant 1 <= i <= a.Length
      invariant forall k :: 0 <= k < i ==> max >= a[k]
      invariant exists k :: 0 <= k < i && max == a[k]
    {
      if a[i] > max {
        max := a[i];
      }
      i := i + 1;
    }
  }
}