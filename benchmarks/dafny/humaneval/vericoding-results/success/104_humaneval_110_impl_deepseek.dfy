// <vc-preamble>

function countEven(lst: seq<int>): int
    ensures countEven(lst) >= 0
    ensures countEven(lst) <= |lst|
{
    if |lst| == 0 then 0
    else if lst[0] % 2 == 0 then 1 + countEven(lst[1..])
    else countEven(lst[1..])
}

predicate ValidInput(lst1: seq<int>, lst2: seq<int>)
{
    |lst1| > 0 && |lst2| > 0
}

predicate CanExchange(lst1: seq<int>, lst2: seq<int>)
{
    countEven(lst1) + countEven(lst2) >= |lst1|
}
// </vc-preamble>

// <vc-helpers>

lemma EvenCountProperty(lst: seq<int>)
    ensures countEven(lst) >= 0
    ensures countEven(lst) <= |lst|
{
}

predicate AllEven(lst: seq<int>)
{
    forall i :: 0 <= i < |lst| ==> lst[i] % 2 == 0
}

lemma ExchangeLemma(lst1: seq<int>, lst2: seq<int>)
    ensures CanExchange(lst1, lst2) == (countEven(lst1) + countEven(lst2) >= |lst1|)
{
}

// </vc-helpers>

// <vc-spec>
method exchange(lst1: seq<int>, lst2: seq<int>) returns (result: string)
    requires ValidInput(lst1, lst2)
    ensures result == "YES" || result == "NO"
    ensures result == "YES" <==> CanExchange(lst1, lst2)
// </vc-spec>
// <vc-code>
{
    if countEven(lst1) + countEven(lst2) >= |lst1| {
        result := "YES";
    } else {
        result := "NO";
    }
}
// </vc-code>
