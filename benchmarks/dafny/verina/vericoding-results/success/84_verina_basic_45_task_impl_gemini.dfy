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
/* helper modified by LLM (iteration 2): added loop invariant to prove index bounds */
method ComputeFirstEvenIndex(lst: array<int>) returns (ei: int)
    requires lst.Length > 0
    requires exists i :: 0 <= i < lst.Length && IsEven(lst[i])
    ensures ei == FirstEvenIndex(lst[..])
{
    var i : nat := 0;
    while i < lst.Length
        decreases lst.Length - i
        invariant 0 <= i <= lst.Length
        invariant forall k :: 0 <= k < i ==> !IsEven(lst[k])
        invariant exists k :: i <= k < lst.Length && IsEven(lst[k])
    {
        if IsEven(lst[i]) {
            ei := i;
            return;
        }
        i := i + 1;
    }
}

/* helper modified by LLM (iteration 2): added loop invariant to prove index bounds */
method ComputeFirstOddIndex(lst: array<int>) returns (oi: int)
    requires lst.Length > 0
    requires exists i :: 0 <= i < lst.Length && IsOdd(lst[i])
    ensures oi == FirstOddIndex(lst[..])
{
    var i : nat := 0;
    while i < lst.Length
        decreases lst.Length - i
        invariant 0 <= i <= lst.Length
        invariant forall k :: 0 <= k < i ==> !IsOdd(lst[k])
        invariant exists k :: i <= k < lst.Length && IsOdd(lst[k])
    {
        if IsOdd(lst[i]) {
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
    /* code modified by LLM (iteration 2): correctly calls helper methods to find indices */
    var ei := ComputeFirstEvenIndex(lst);
    var oi := ComputeFirstOddIndex(lst);
    result := lst[ei] * lst[oi];
}
// </vc-code>
