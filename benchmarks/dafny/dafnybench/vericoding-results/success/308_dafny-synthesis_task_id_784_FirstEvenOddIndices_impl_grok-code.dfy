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

// <vc-helpers>
// No changes needed in helpers
// </vc-helpers>

// <vc-spec>
method FirstEvenOddIndices(lst : seq<int>) returns (evenIndex: int, oddIndex : int)
    requires |lst| >= 2
    requires exists i :: 0 <= i < |lst| && IsEven(lst[i])
    requires exists i :: 0 <= i < |lst| && IsOdd(lst[i])
    ensures 0 <= evenIndex < |lst|
    ensures 0 <= oddIndex < |lst|
    // This is the postcondition that ensures that it's the first, not just any
    ensures IsEven(lst[evenIndex]) && IsFirstEven(evenIndex, lst)
    ensures IsOdd(lst[oddIndex]) && IsFirstOdd(oddIndex, lst)
// </vc-spec>
// <vc-code>
{
  var evIdx := 0;
  while evIdx < |lst| && !IsEven(lst[evIdx])
    invariant 0 <= evIdx <= |lst|
    invariant forall k :: 0 <= k < evIdx ==> IsOdd(lst[k])
  {
    assert !IsEven(lst[evIdx]);
    evIdx := evIdx + 1;
  }
  evenIndex := evIdx;
  assert evenIndex < |lst|;

  var oddIdx := 0;
  while oddIdx < |lst| && !IsOdd(lst[oddIdx])
    invariant 0 <= oddIdx <= |lst|
    invariant forall k :: 0 <= k < oddIdx ==> IsEven(lst[k])
  {
    assert !IsOdd(lst[oddIdx]);
    oddIdx := oddIdx + 1;
  }
  oddIndex := oddIdx;
  assert oddIndex < |lst|;

}
// </vc-code>

