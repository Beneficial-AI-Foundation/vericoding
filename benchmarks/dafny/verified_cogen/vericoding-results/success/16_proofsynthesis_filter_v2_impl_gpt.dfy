// <vc-preamble>
function filter(s: seq<int>, p: int -> bool): seq<int>
{
    if |s| == 0 then []
    else if p(s[0]) then [s[0]] + filter(s[1..], p)
    else filter(s[1..], p)
}
// </vc-preamble>

// <vc-helpers>
predicate DivisibleBy3(k: int) { k % 3 == 0 }
// </vc-helpers>

// <vc-spec>
method myfun4(x: seq<int>) returns (y: seq<int>)
    ensures y == filter(x, k => k % 3 == 0)
// </vc-spec>
// <vc-code>
{
  y := filter(x, k => k % 3 == 0);
}
// </vc-code>
