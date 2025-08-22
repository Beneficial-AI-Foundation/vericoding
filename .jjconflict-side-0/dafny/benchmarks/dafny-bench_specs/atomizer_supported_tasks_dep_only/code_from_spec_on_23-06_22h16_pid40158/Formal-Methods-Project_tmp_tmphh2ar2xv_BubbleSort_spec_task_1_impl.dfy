//ATOM sorted
predicate sorted(a: array?<int>)
  reads a
{
  a != null ==> forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}

//ATOM partitioned
predicate partitioned(a: array?<int>, pivot: int)
  reads a
{
  a != null ==> forall i, j :: 0 <= i < pivot < j < a.Length ==> a[i] <= a[j]
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
  
  /* code modified by LLM (iteration 4): Fixed outer loop invariants to properly establish sorted suffix property */
  while i < n - 1
    invariant 0 <= i <= n - 1
    invariant multiset(a[..]) == multiset(old(a[..]))
    invariant forall k1, k2 :: n - i <= k1 < k2 < n ==> a[k1] <= a[k2]
    invariant forall k1, k2 :: 0 <= k1 < n - i && n - i <= k2 < n ==> a[k1] <= a[k2]
  {
    var j := 0;
    
    /* code modified by LLM (iteration 4): Fixed inner loop invariants to track maximum element bubbling */
    while j < n - 1 - i
      invariant 0 <= j <= n - 1 - i
      invariant multiset(a[..]) == multiset(old(a[..]))
      invariant forall k1, k2 :: n - i <= k1 < k2 < n ==> a[k1] <= a[k2]
      invariant forall k1, k2 :: 0 <= k1 < n - i && n - i <= k2 < n ==> a[k1] <= a[k2]
      invariant forall k :: 0 <= k < j ==> a[k] <= a[j]
      invariant forall k :: n - i <= k < n ==> a[j] <= a[k]
    {
      if a[j] > a[j + 1] {
        var temp := a[j];
        a[j] := a[j + 1];
        a[j + 1] := temp;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}

//ATOM Main
method Main()
{
  var a := new int[5];
  a[0] := 5;
  a[1] := 2;
  a[2] := 8;
  a[3] := 1;
  a[4] := 9;
  
  print "Before sorting: ";
  var i := 0;
  while i < a.Length {
    print a[i], " ";
    i := i + 1;
  }
  print "\n";
  
  BubbleSort(a);
  
  print "After sorting: ";
  i := 0;
  while i < a.Length {
    print a[i], " ";
    i := i + 1;
  }
  print "\n";
}