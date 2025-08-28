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
lemma FirstEvenExists(lst: seq<int>)
    requires exists i :: 0 <= i < |lst| && IsEven(lst[i])
    ensures exists i :: 0 <= i < |lst| && IsEven(lst[i]) && IsFirstEven(i, lst)
{
    var minIndex := FindMinIndex(lst, IsEven);
    assert IsEven(lst[minIndex]);
    assert IsFirstEven(minIndex, lst);
}

lemma FirstOddExists(lst: seq<int>)
    requires exists i :: 0 <= i < |lst| && IsOdd(lst[i])
    ensures exists i :: 0 <= i < |lst| && IsOdd(lst[i]) && IsFirstOdd(i, lst)
{
    var minIndex := FindMinIndex(lst, IsOdd);
    assert IsOdd(lst[minIndex]);
    assert IsFirstOdd(minIndex, lst);
}

function FindMinIndex<T>(lst: seq<T>, p: T -> bool): int
    requires exists i :: 0 <= i < |lst| && p(lst[i])
    ensures 0 <= FindMinIndex(lst, p) < |lst|
    ensures p(lst[FindMinIndex(lst, p)])
    ensures forall i :: 0 <= i < FindMinIndex(lst, p) ==> !p(lst[i])
{
    FindMinIndexHelper(lst, p, 0)
}

function FindMinIndexHelper<T>(lst: seq<T>, p: T -> bool, start: int): int
    requires 0 <= start <= |lst|
    requires exists i :: start <= i < |lst| && p(lst[i])
    ensures start <= FindMinIndexHelper(lst, p, start) < |lst|
    ensures p(lst[FindMinIndexHelper(lst, p, start)])
    ensures forall i :: start <= i < FindMinIndexHelper(lst, p, start) ==> !p(lst[i])
    decreases |lst| - start
{
    if p(lst[start]) then start
    else FindMinIndexHelper(lst, p, start + 1)
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>

// <vc-code>
{
    FirstEvenExists(lst);
    FirstOddExists(lst);
    evenIndex := FindMinIndex(lst, IsEven);
    oddIndex := FindMinIndex(lst, IsOdd);
}
// </vc-code>
