// <vc-preamble>
predicate IsEven(n: int)
{
    n % 2 == 0
}

predicate IsOdd(n: int)
{
    n % 2 != 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added decreases clauses to ensure loop termination */
method FindFirstEven(a: array<int>) returns (index: int, value: int)
    requires exists x :: 0 <= x < a.Length && IsEven(a[x])
    ensures 0 <= index < a.Length && IsEven(a[index]) && value == a[index]
    ensures forall k :: 0 <= k < index ==> IsOdd(a[k])
{
    index := 0;
    while !IsEven(a[index])
        decreases a.Length - index
        invariant 0 <= index < a.Length
        invariant forall k :: 0 <= k < index ==> !IsEven(a[k])
        invariant exists k :: index <= k < a.Length && IsEven(a[k])
    {
        index := index + 1;
    }
    value := a[index];
}

/* helper modified by LLM (iteration 3): added decreases clauses to ensure loop termination */
method FindFirstOdd(a: array<int>) returns (index: int, value: int)
    requires exists x :: 0 <= x < a.Length && IsOdd(a[x])
    ensures 0 <= index < a.Length && IsOdd(a[index]) && value == a[index]
    ensures forall k :: 0 <= k < index ==> IsEven(a[k])
{
    index := 0;
    while !IsOdd(a[index])
        decreases a.Length - index
        invariant 0 <= index < a.Length
        invariant forall k :: 0 <= k < index ==> !IsOdd(a[k])
        invariant exists k :: index <= k < a.Length && IsOdd(a[k])
    {
        index := index + 1;
    }
    value := a[index];
}
// </vc-helpers>

// <vc-spec>
method FirstEvenOddDifference(a: array<int>) returns (result: int)
    requires 
        a.Length > 1 &&
        (exists x :: 0 <= x < a.Length && IsEven(a[x])) &&
        (exists x :: 0 <= x < a.Length && IsOdd(a[x]))
    ensures 
        exists i, j :: 
            0 <= i < a.Length && 0 <= j < a.Length &&
            IsEven(a[i]) && IsOdd(a[j]) &&
            result == a[i] - a[j] &&
            (forall k :: 0 <= k < i ==> IsOdd(a[k])) &&
            (forall k :: 0 <= k < j ==> IsEven(a[k]))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): using helper methods with termination guarantees */
    var evenIndex, evenValue := FindFirstEven(a);
    var oddIndex, oddValue := FindFirstOdd(a);
    result := evenValue - oddValue;
}
// </vc-code>
