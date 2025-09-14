predicate IsEven(n: int)
{
    n % 2 == 0
}

predicate IsOdd(n: int)
{
    n % 2 != 0
}

predicate IsFirstEven(evenIndex: int, lst: seq<int>)
    requires 0 <= evenIndex < |lst|
    requires IsEven(lst[evenIndex])
{
    forall i :: 0 <= i < evenIndex ==> IsOdd(lst[i])
}

predicate IsFirstOdd(oddIndex: int, lst: seq<int>)
    requires 0 <= oddIndex < |lst|
    requires IsOdd(lst[oddIndex])
{
    forall i :: 0 <= i < oddIndex ==> IsEven(lst[i])
}


method FirstEvenOddIndices(lst : seq<int>) returns (evenIndex: int, oddIndex : int)
    requires |lst| >= 2
    requires exists i :: 0 <= i < |lst| && IsEven(lst[i])
    requires exists i :: 0 <= i < |lst| && IsOdd(lst[i])
    ensures 0 <= evenIndex < |lst|
    ensures 0 <= oddIndex < |lst|
    // This is the postcondition that ensures that it's the first, not just any
    ensures IsEven(lst[evenIndex]) && IsFirstEven(evenIndex, lst)
    ensures IsOdd(lst[oddIndex]) && IsFirstOdd(oddIndex, lst)
{
  assume{:axiom} false;
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ProductEvenOdd(lst: seq<int>) returns (product : int)
    requires |lst| >= 2
    requires exists i :: 0 <= i < |lst| && IsEven(lst[i])
    requires exists i :: 0 <= i < |lst| && IsOdd(lst[i])
    ensures exists i, j :: 0 <= i < |lst| && IsEven(lst[i]) && IsFirstEven(i, lst) && 
                           0 <= j < |lst| && IsOdd(lst[j])  && IsFirstOdd(j, lst) && product == lst[i] * lst[j]
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < |lst| && IsOdd(lst[i])
    invariant 0 <= i <= |lst|
    invariant forall k :: 0 <= k < i ==> IsOdd(lst[k])
    invariant exists k :: i <= k < |lst| && IsEven(lst[k])
    decreases |lst| - i
  {
    i := i + 1;
  }
  assert i < |lst|;
  assert IsEven(lst[i]);
  var evenIndex := i;

  var j := 0;
  while j < |lst| && IsEven(lst[j])
    invariant 0 <= j <= |lst|
    invariant forall k :: 0 <= k < j ==> IsEven(lst[k])
    invariant exists k :: j <= k < |lst| && IsOdd(lst[k])
    decreases |lst| - j
  {
    j := j + 1;
  }
  assert j < |lst|;
  assert IsOdd(lst[j]);
  var oddIndex := j;

  assert IsFirstEven(evenIndex, lst);
  assert IsFirstOdd(oddIndex, lst);

  product := lst[evenIndex] * lst[oddIndex];
}
// </vc-code>

