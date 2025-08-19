method FindZero(a: array<int>) returns (index: int)
  /* code modified by LLM (iteration 1): removed redundant null check since array<int> is non-null by default */
  requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
  requires forall i :: 0 < i < a.Length ==> a[i-1]-1 <= a[i]
  ensures index < 0 ==> forall i :: 0 <= i < a.Length ==> a[i] != 0
  ensures 0 <= index ==> index < a.Length && a[index] == 0
{
  index := -1;
  
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant index < 0 ==> forall j :: 0 <= j < i ==> a[j] != 0
    invariant index >= 0 ==> index < a.Length && a[index] == 0
  {
    if a[i] == 0 {
      index := i;
      return;
    }
  }
}