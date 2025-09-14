// <vc-preamble>
function filter(s: seq<int>, p: int -> bool): seq<int>
{
    if |s| == 0 then []
    else if p(s[0]) then [s[0]] + filter(s[1..], p)
    else filter(s[1..], p)
}
// </vc-preamble>

// <vc-helpers>
function IsDivisibleBy3(k: int): bool { k % 3 == 0 }

lemma FilterLemma(s: seq<int>, p: int -> bool)
  ensures |filter(s, p)| <= |s|
{
  if |s| != 0 {
    FilterLemma(s[1..], p);
  }
}
// </vc-helpers>

// <vc-spec>
method myfun4(x: seq<int>) returns (y: seq<int>)
    ensures y == filter(x, k => k % 3 == 0)
// </vc-spec>
// <vc-code>
{
  if |x| == 0 {
    y := [];
    return;
  }
  var rest: seq<int>;
  rest := myfun4(x[1..]);
  if x[0] % 3 == 0 {
    y := [x[0]] + rest;
  } else {
    y := rest;
  }
}
// </vc-code>
