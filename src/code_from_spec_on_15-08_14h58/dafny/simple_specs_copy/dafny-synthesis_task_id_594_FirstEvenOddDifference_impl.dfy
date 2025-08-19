predicate IsEven(n: int)
{
  n % 2 == 0
}

//ATOM
predicate IsOdd(n: int)
{
  n % 2 != 0
}

//IMPL
method FirstEvenOddDifference(a: array<int>) returns (diff: int)
  requires a.Length >= 2
  requires exists i :: 0 <= i < a.Length && IsEven(a[i])
  requires exists i :: 0 <= i < a.Length && IsOdd(a[i])
  /* code modified by LLM (iteration 4): Fixed indentation warning by properly formatting the ensures clause */
  ensures exists i, j :: 0 <= i < a.Length && 0 <= j < a.Length && IsEven(a[i]) && IsOdd(a[j]) && diff == a[i] - a[j] && 
            (forall k :: 0 <= k < i ==> IsOdd(a[k])) && (forall k :: 0 <= k < j ==> IsEven(a[k]))
{
  var firstEven := -1;
  var firstOdd := -1;
  var i := 0;
  
  while i < a.Length && (firstEven == -1 || firstOdd == -1)
    invariant 0 <= i <= a.Length
    invariant firstEven == -1 ==> forall k :: 0 <= k < i ==> IsOdd(a[k])
    invariant firstEven != -1 ==> 0 <= firstEven < i && IsEven(a[firstEven]) && (forall k :: 0 <= k < firstEven ==> IsOdd(a[k]))
    invariant firstOdd == -1 ==> forall k :: 0 <= k < i ==> IsEven(a[k])
    invariant firstOdd != -1 ==> 0 <= firstOdd < i && IsOdd(a[firstOdd]) && (forall k :: 0 <= k < firstOdd ==> IsEven(a[k]))
  {
    if firstEven == -1 && IsEven(a[i]) {
      firstEven := i;
    }
    if firstOdd == -1 && IsOdd(a[i]) {
      firstOdd := i;
    }
    i := i + 1;
  }
  
  diff := a[firstEven] - a[firstOdd];
}