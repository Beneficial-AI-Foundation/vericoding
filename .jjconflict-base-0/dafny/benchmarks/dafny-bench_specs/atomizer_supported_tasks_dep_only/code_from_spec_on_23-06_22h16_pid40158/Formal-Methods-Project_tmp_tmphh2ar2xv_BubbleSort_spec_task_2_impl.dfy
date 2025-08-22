//ATOM sorted
predicate sorted(a: array?<int>)
  reads a
  requires a != null
{
  forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}

//ATOM partitioned
predicate partitioned(a: array?<int>, pivot: int)
  reads a
  requires a != null
{
  forall i, j :: 0 <= i < pivot < j < a.Length ==> a[i] <= a[j]
}

//IMPL BubbleSort
method BubbleSort(a: array?<int>)
  modifies a
  requires a != null
  ensures sorted(a)
  ensures multiset(a[..]) == multiset(old(a[..]))
{
  if a.Length <= 1 {
    return;
  }
  
  var n := a.Length;
  var i := 0;
  
  /* code modified by LLM (iteration 2): Corrected outer loop invariants to properly establish sorted suffix */
  while i < n - 1
    invariant 0 <= i <= n - 1
    invariant multiset(a[..]) == multiset(old(a[..]))
    invariant forall k, l :: n - i <= k < l < n ==> a[k] <= a[l]
    invariant forall k, l :: 0 <= k < n - i && n - i <= l < n ==> a[k] <= a[l]
  {
    var j := 0;
    
    /* code modified by LLM (iteration 2): Fixed inner loop invariants to properly track the bubbling process */
    while j < n - 1 - i
      invariant 0 <= j <= n - 1 - i
      invariant multiset(a[..]) == multiset(old(a[..]))
      invariant forall k, l :: n - i <= k < l < n ==> a[k] <= a[l]
      invariant forall k, l :: 0 <= k < n - i && n - i <= l < n ==> a[k] <= a[l]
      invariant forall k :: 0 <= k <= j ==> a[k] <= a[j]
    {
      if a[j] > a[j + 1] {
        /* code modified by LLM (iteration 2): Swap elements to maintain bubbling property */
        var temp := a[j];
        a[j] := a[j + 1];
        a[j + 1] := temp;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}

//IMPL Main
method Main() {
  var arr := new int[5];
  arr[0] := 5;
  arr[1] := 2;
  arr[2] := 8;
  arr[3] := 1;
  arr[4] := 9;
  
  BubbleSort(arr);
  
  print "Sorted array: ";
  var i := 0;
  while i < arr.Length {
    print arr[i];
    if i < arr.Length - 1 {
      print ", ";
    }
    i := i + 1;
  }
  print "\n";
}