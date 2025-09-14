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
  var i := 0;
  evenIndex := -1;
  oddIndex := -1;

  while i < |lst|
    invariant 0 <= i <= |lst|
    invariant evenIndex == -1 ==> (forall j :: 0 <= j < i ==> IsOdd(lst[j]))
    invariant evenIndex != -1 ==> 0 <= evenIndex < i && IsEven(lst[evenIndex]) && (forall j :: 0 <= j < evenIndex ==> IsOdd(lst[j]))
    invariant oddIndex == -1 ==> (forall j :: 0 <= j < i ==> IsEven(lst[j]))
    invariant oddIndex != -1 ==> 0 <= oddIndex < i && IsOdd(lst[oddIndex]) && (forall j :: 0 <= j < oddIndex ==> IsEven(lst[j]))
    decreases |lst| - i
  {
    if evenIndex == -1 {
      if IsEven(lst[i]) {
        evenIndex := i;
      } else {
        assert IsOdd(lst[i]);
      }
    }
    if oddIndex == -1 {
      if IsOdd(lst[i]) {
        oddIndex := i;
      } else {
        assert IsEven(lst[i]);
      }
    }
    i := i + 1;
  }

  assert i >= |lst|;
  assert i <= |lst|;
  assert i == |lst|;

  if evenIndex == -1 {
    var jEven: int :| 0 <= jEven < |lst| && IsEven(lst[jEven]);
    assert jEven < i;
    assert IsOdd(lst[jEven]);
    assert false;
  }
  if oddIndex == -1 {
    var jOdd: int :| 0 <= jOdd < |lst| && IsOdd(lst[jOdd]);
    assert jOdd < i;
    assert IsEven(lst[jOdd]);
    assert false;
  }
}
// </vc-code>

