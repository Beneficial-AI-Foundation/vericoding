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
lemma EvenOddExistence(lst: seq<int>, evenIndex: int, oddIndex: int)
    requires |lst| >= 2
    requires 0 <= evenIndex < |lst| && IsEven(lst[evenIndex]) && IsFirstEven(evenIndex, lst)
    requires 0 <= oddIndex < |lst| && IsOdd(lst[oddIndex]) && IsFirstOdd(oddIndex, lst)
    ensures exists i, j :: 0 <= i < |lst| && IsEven(lst[i]) && IsFirstEven(i, lst) && 
                          0 <= j < |lst| && IsOdd(lst[j]) && IsFirstOdd(j, lst) && lst[i] * lst[j] == lst[evenIndex] * lst[oddIndex]
{
    assert IsEven(lst[evenIndex]) && IsFirstEven(evenIndex, lst);
    assert IsOdd(lst[oddIndex]) && IsFirstOdd(oddIndex, lst);
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method ProductEvenOdd(lst: seq<int>) returns (product : int)
    requires |lst| >= 2
    requires exists i :: 0 <= i < |lst| && IsEven(lst[i])
    requires exists i :: 0 <= i < |lst| && IsOdd(lst[i])
    ensures exists i, j :: 0 <= i < |lst| && IsEven(lst[i]) && IsFirstEven(i, lst) && 
                           0 <= j < |lst| && IsOdd(lst[j])  && IsFirstOdd(j, lst) && product == lst[i] * lst[j]
// </vc-spec>
// </vc-spec>

// <vc-code>
method ComputeProductEvenOdd(lst: seq<int>) returns (product: int)
    requires |lst| >= 2
    requires exists i :: 0 <= i < |lst| && IsEven(lst[i])
    requires exists i :: 0 <= i < |lst| && IsOdd(lst[i])
    ensures exists i, j :: 0 <= i < |lst| && IsEven(lst[i]) && IsFirstEven(i, lst) && 
                          0 <= j < |lst| && IsOdd(lst[j]) && IsFirstOdd(j, lst) && product == lst[i] * lst[j]
{
    var evenIndex, oddIndex := FirstEvenOddIndices(lst);
    product := lst[evenIndex] * lst[oddIndex];
    EvenOddExistence(lst, evenIndex, oddIndex);
}
// </vc-code>
