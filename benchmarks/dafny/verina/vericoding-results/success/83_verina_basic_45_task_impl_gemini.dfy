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
method FindFirstEven(lst: array<int>) returns (ei: int)
    requires lst.Length > 0
    requires exists i :: 0 <= i < lst.Length && IsEven(lst[i])
    ensures 0 <= ei < lst.Length && IsEven(lst[ei])
    ensures forall j :: 0 <= j < ei ==> !IsEven(lst[j])
{
    var i := 0;
    while i < lst.Length
        invariant 0 <= i <= lst.Length
        invariant forall j :: 0 <= j < i ==> !IsEven(lst[j])
    {
        if IsEven(lst[i])
        {
            ei := i;
            return;
        }
        i := i + 1;
    }
}

method FindFirstOdd(lst: array<int>) returns (oi: int)
    requires lst.Length > 0
    requires exists i :: 0 <= i < lst.Length && IsOdd(lst[i])
    ensures 0 <= oi < lst.Length && IsOdd(lst[oi])
    ensures forall j :: 0 <= j < oi ==> !IsOdd(lst[j])
{
    var i := 0;
    while i < lst.Length
        invariant 0 <= i <= lst.Length
        invariant forall j :: 0 <= j < i ==> !IsOdd(lst[j])
    {
        if IsOdd(lst[i])
        {
            oi := i;
            return;
        }
        i := i + 1;
    }
}
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
    var ei := FindFirstEven(lst);
    var oi := FindFirstOdd(lst);
    result := lst[ei] * lst[oi];
}
// </vc-code>
