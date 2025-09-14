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
lemma Lemma_FirstEvenExists(lst: seq<int>)
    requires |lst| >= 2
    requires exists i :: 0 <= i < |lst| && IsEven(lst[i])
    ensures exists i :: 0 <= i < |lst| && IsEven(lst[i]) && IsFirstEven(i, lst)
{
    var i := 0;
    while i < |lst|
        invariant 0 <= i <= |lst|
        invariant forall k :: 0 <= k < i ==> IsOdd(lst[k])
    {
        if IsEven(lst[i]) {
            assert IsFirstEven(i, lst);
            return;
        }
        i := i + 1;
    }
}

lemma Lemma_FirstOddExists(lst: seq<int>)
    requires |lst| >= 2
    requires exists i :: 0 <= i < |lst| && IsOdd(lst[i])
    ensures exists i :: 0 <= i < |lst| && IsOdd(lst[i]) && IsFirstOdd(i, lst)
{
    var i := 0;
    while i < |lst|
        invariant 0 <= i <= |lst|
        invariant forall k :: 0 <= k < i ==> IsEven(lst[k])
    {
        if IsOdd(lst[i]) {
            assert IsFirstOdd(i, lst);
            return;
        }
        i := i + 1;
    }
}
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
    var evenIndex, oddIndex := FirstEvenOddIndices(lst);
    Lemma_FirstEvenExists(lst);
    Lemma_FirstOddExists(lst);
    product := lst[evenIndex] * lst[oddIndex];
}
// </vc-code>

