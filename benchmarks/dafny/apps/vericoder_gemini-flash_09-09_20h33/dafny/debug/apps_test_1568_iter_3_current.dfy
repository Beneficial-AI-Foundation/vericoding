predicate ValidInput(n: int, a: int, b: int, c: int, t: int, arrivals: seq<int>) 
{
    1 <= n <= 1000 &&
    1 <= a <= 1000 &&
    1 <= b <= 1000 &&
    1 <= c <= 1000 &&
    1 <= t <= 1000 &&
    |arrivals| == n &&
    forall i :: 0 <= i < |arrivals| ==> 1 <= arrivals[i] <= t
}

function sum_seq(s: seq<int>): int
{
    if |s| == 0 then 0
    else s[0] + sum_seq(s[1..])
}

function MaxMoney(n: int, a: int, b: int, c: int, t: int, arrivals: seq<int>): int
    requires ValidInput(n, a, b, c, t, arrivals)
{
    if b > c then n * a
    else n * a + (c - b) * (n * t - sum_seq(arrivals))
}

// <vc-helpers>
function sum_seq_iter(s: seq<int>): int
{
  var total := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant total == sum_seq(s[..i])
  {
    total := total + s[i];
    i := i + 1;
  }
  return total;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: int, b: int, c: int, t: int, arrivals: seq<int>) returns (result: int)
    requires ValidInput(n, a, b, c, t, arrivals)
    ensures result == MaxMoney(n, a, b, c, t, arrivals)
// </vc-spec>
// <vc-code>
{
  if b > c {
    return n * a;
  } else {
    var sum_arrivals := sum_seq_iter(arrivals);
    return n * a + (c - b) * (n * t - sum_arrivals);
  }
}
// </vc-code>

