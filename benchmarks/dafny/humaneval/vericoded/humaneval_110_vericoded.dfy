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

// </vc-helpers>

// <vc-spec>
method exchange(lst1: seq<int>, lst2: seq<int>) returns (result: string)
    requires ValidInput(lst1, lst2)
    ensures result == "YES" || result == "NO"
    ensures result == "YES" <==> CanExchange(lst1, lst2)
// </vc-spec>
// <vc-code>
{
  var evenCount1 := countEven(lst1);
  var evenCount2 := countEven(lst2);
  if evenCount1 + evenCount2 >= |lst1| {
    result := "YES";
  } else {
    result := "NO";
  }
}
// </vc-code>
