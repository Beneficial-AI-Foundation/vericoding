// <vc-preamble>
// ======= TASK =======
// Given two non-empty lists of numbers, determine if it's possible to exchange
// elements between them such that the first list contains only even numbers.
// Return "YES" if possible, "NO" otherwise.

// ======= SPEC REQUIREMENTS =======
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
// ======= HELPERS =======
// </vc-helpers>

// <vc-spec>
// ======= MAIN METHOD =======
method exchange(lst1: seq<int>, lst2: seq<int>) returns (result: string)
    requires ValidInput(lst1, lst2)
    ensures result == "YES" || result == "NO"
    ensures result == "YES" <==> CanExchange(lst1, lst2)
// </vc-spec>
// <vc-code>
{
    var tmpCall1 := countEven(lst1);
    var tmpCall2 := countEven(lst2);
    var totalEven := tmpCall1 + tmpCall2;
    if totalEven >= |lst1| {
        result := "YES";
    } else {
        result := "NO";
    }
}
// </vc-code>
