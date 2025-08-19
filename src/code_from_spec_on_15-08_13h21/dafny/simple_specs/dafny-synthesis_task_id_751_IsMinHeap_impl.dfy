//IMPL 
method IsMinHeap(a: array<int>) returns (result: bool)
  /* code modified by LLM (iteration 1): removed redundant null check since array<int> is non-null by default */
  ensures result ==> forall i :: 0 <= i < a.Length / 2 ==> a[i] <= a[2*i + 1] && (2*i + 2 == a.Length || a[i] <= a[2*i + 2])
  ensures !result ==> exists i :: 0 <= i < a.Length / 2 && (a[i] > a[2*i + 1] || (2*i + 2 != a.Length && a[i] > a[2*i + 2]))
{
  result := true;
  var i := 0;
  
  while i < a.Length / 2
    invariant 0 <= i <= a.Length / 2
    invariant result ==> forall j :: 0 <= j < i ==> a[j] <= a[2*j + 1] && (2*j + 2 == a.Length || a[j] <= a[2*j + 2])
    invariant !result ==> exists j :: 0 <= j < i && (a[j] > a[2*j + 1] || (2*j + 2 != a.Length && a[j] > a[2*j + 2]))
  {
    if a[i] > a[2*i + 1] || (2*i + 2 != a.Length && a[i] > a[2*i + 2]) {
      result := false;
      return;
    }
    i := i + 1;
  }
}