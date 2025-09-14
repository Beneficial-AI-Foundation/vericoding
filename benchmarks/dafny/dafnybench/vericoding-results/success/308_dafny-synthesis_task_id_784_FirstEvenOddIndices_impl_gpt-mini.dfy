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
// No helpers needed.
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
  evenIndex := -1;
  oddIndex := -1;
  var i := 0;
  while i < |lst| && (evenIndex == -1 || oddIndex == -1)
    invariant 0 <= i <= |lst|
    invariant -1 <= evenIndex < |lst|
    invariant -1 <= oddIndex < |lst|
    invariant evenIndex == -1 ==> forall k :: 0 <= k < i ==> IsOdd(lst[k])
    invariant oddIndex == -1 ==> forall k :: 0 <= k < i ==> IsEven(lst[k])
    invariant evenIndex != -1 ==> 0 <= evenIndex < i && IsEven(lst[evenIndex]) && (forall k :: 0 <= k < evenIndex ==> IsOdd(lst[k]))
    invariant oddIndex != -1 ==> 0 <= oddIndex < i && IsOdd(lst[oddIndex]) && (forall k :: 0 <= k < oddIndex ==> IsEven(lst[k]))
    decreases |lst| - i
  {
    if evenIndex == -1 && IsEven(lst[i]) {
      evenIndex := i;
    }
    if oddIndex == -1 && IsOdd(lst[i]) {
      oddIndex := i;
    }
    i := i + 1;
  }
  // At this point, by the preconditions there must be both an even and an odd in lst,
  // and the loop invariants ensure the indices found (if set) are the first occurrences.
  // Ensure both are set.
  assert evenIndex != -1;
  assert oddIndex != -1;
}
// </vc-code>

