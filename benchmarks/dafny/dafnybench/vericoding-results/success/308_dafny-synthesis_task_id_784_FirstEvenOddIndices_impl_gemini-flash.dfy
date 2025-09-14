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
// The original predicates defined outside the vc-helpers block are already sufficient.
// No additional helper predicates are needed nor should be duplicated.
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
    var even := -1;
    var odd := -1;

    var i := 0;
    while i < |lst|
        invariant 0 <= i <= |lst|
        invariant (even != -1) ==> (0 <= even < i && IsEven(lst[even]) && IsFirstEven(even, lst))
        invariant (odd != -1) ==> (0 <= odd < i && IsOdd(lst[odd]) && IsFirstOdd(odd, lst))
        invariant (even == -1) ==> (forall k :: 0 <= k < i ==> IsOdd(lst[k]))
        invariant (odd == -1) ==> (forall k :: 0 <= k < i ==> IsEven(lst[k]))
        decreases |lst| - i
    {
        if even == -1 && IsEven(lst[i]) {
            even := i;
        } else if odd == -1 && IsOdd(lst[i]) {
            odd := i;
        }
        i := i + 1;
    }
    return even, odd;
}
// </vc-code>

