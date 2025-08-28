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
lemma EvenOddExistence(lst: seq<int>)
    requires |lst| >= 2
    requires exists i :: 0 <= i < |lst| && IsEven(lst[i])
    requires exists i :: 0 <= i < |lst| && IsOdd(lst[i])
    ensures exists i, j :: 0 <= i < |lst| && 0 <= j < |lst| && IsEven(lst[i]) && IsOdd(lst[j])
{
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
method FirstEvenOddIndicesImpl(lst: seq<int>) returns (evenIndex: int, oddIndex: int)
    requires |lst| >= 2
    requires exists i :: 0 <= i < |lst| && IsEven(lst[i])
    requires exists i :: 0 <= i < |lst| && IsOdd(lst[i])
    ensures 0 <= evenIndex < |lst|
    ensures 0 <= oddIndex < |lst|
    ensures IsEven(lst[evenIndex]) && IsFirstEven(evenIndex, lst)
    ensures IsOdd(lst[oddIndex]) && IsFirstOdd(oddIndex, lst)
{
    evenIndex := -1;
    oddIndex := -1;
    
    for i := 0 to |lst|
        invariant 0 <= i <= |lst|
        invariant evenIndex == -1 ==> forall k :: 0 <= k < i ==> IsOdd(lst[k])
        invariant oddIndex == -1 ==> forall k :: 0 <= k < i ==> IsEven(lst[k])
        invariant evenIndex != -1 ==> 0 <= evenIndex < i && IsEven(lst[evenIndex]) && IsFirstEven(evenIndex, lst)
        invariant oddIndex != -1 ==> 0 <= oddIndex < i && IsOdd(lst[oddIndex]) && IsFirstOdd(oddIndex, lst)
    {
        if evenIndex == -1 && IsEven(lst[i]) {
            evenIndex := i;
        }
        if oddIndex == -1 && IsOdd(lst[i]) {
            oddIndex := i;
        }
        if evenIndex != -1 && oddIndex != -1 {
            break;
        }
    }
    
    assert evenIndex != -1 && oddIndex != -1;
}
// </vc-code>
