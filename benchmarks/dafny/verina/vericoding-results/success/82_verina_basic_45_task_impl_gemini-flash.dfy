// <vc-preamble>
predicate FindProductPrecond(lst: seq<int>)
{
    |lst| > 1 &&
    (exists x :: x in lst && IsEven(x)) &&
    (exists x :: x in lst && IsOdd(x))
}
predicate IsEven(n: int)
{
    n % 2 == 0
}

predicate IsOdd(n: int)
{
    n % 2 != 0
}

function {:axiom} FirstEvenIndex(lst: seq<int>): int
    requires exists i :: 0 <= i < |lst| && IsEven(lst[i])
    ensures 0 <= FirstEvenIndex(lst) < |lst|
    ensures IsEven(lst[FirstEvenIndex(lst)])
    ensures forall j :: 0 <= j < FirstEvenIndex(lst) ==> !IsEven(lst[j])

function {:axiom} FirstOddIndex(lst: seq<int>): int
    requires exists i :: 0 <= i < |lst| && IsOdd(lst[i])
    ensures 0 <= FirstOddIndex(lst) < |lst|
    ensures IsOdd(lst[FirstOddIndex(lst)])
    ensures forall j :: 0 <= j < FirstOddIndex(lst) ==> !IsOdd(lst[j])
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method FindProduct(lst: array<int>) returns (result: int)
    requires lst.Length > 1
    requires exists x :: x in lst[..] && IsEven(x)
    requires exists x :: x in lst[..] && IsOdd(x)
    ensures var ei := FirstEvenIndex(lst[..]);
            var oi := FirstOddIndex(lst[..]);
            result == lst[ei] * lst[oi]
// </vc-spec>
// <vc-code>
{
    var evenIndex: int := 0;
    var oddIndex: int := 0;

    // Find the first even number and its index
    var i: int := 0;
    while i < lst.Length
        invariant 0 <= i <= lst.Length
        invariant forall k :: 0 <= k < i ==> !IsEven(lst[k])
        decreases lst.Length - i
    {
        if IsEven(lst[i]) {
            evenIndex := i;
            break;
        }
        i := i + 1;
    }

    // Find the first odd number and its index
    var j: int := 0;
    while j < lst.Length
        invariant 0 <= j <= lst.Length
        invariant forall k :: 0 <= k < j ==> !IsOdd(lst[k])
        decreases lst.Length - j
    {
        if IsOdd(lst[j]) {
            oddIndex := j;
            break;
        }
        j := j + 1;
    }

    result := lst[evenIndex] * lst[oddIndex];
}
// </vc-code>
