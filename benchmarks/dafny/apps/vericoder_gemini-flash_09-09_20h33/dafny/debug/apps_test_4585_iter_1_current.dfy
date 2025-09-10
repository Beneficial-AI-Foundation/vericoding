predicate ValidInput(x: int)
{
  x >= 1
}

function TriangularNumber(n: int): int
  requires n >= 0
{
  n * (n + 1) / 2
}

predicate IsMinimalTime(t: int, x: int)
  requires x >= 1
{
  t >= 1 && 
  TriangularNumber(t) >= x &&
  (t == 1 || TriangularNumber(t - 1) < x)
}

// <vc-helpers>
function find_minimal_t(x: int): int
  requires x >= 1
  ensures IsMinimalTime(find_minimal_t(x), x)
{
  var low := 1;
  var high := x; // A loose upper bound, since TriangularNumber(x) >= x. Or even x if x >= 1.
  var result := high;

  while low <= high
    invariant low >= 1
    invariant high >= 0
    invariant result >= 1
    invariant TriangularNumber(result) >= x
    invariant forall k :: low <= k <= high ==> TriangularNumber(k) >= x ==> result <= k // If some TriangularNumber(k) >= x in the search range, then result is at least as good as k.
    invariant forall k :: 1 <= k < low ==> TriangularNumber(k) < x // All numbers less than low are too small
  {
    var mid := low + (high - low) / 2;
    if TriangularNumber(mid) >= x
    {
      result := mid;
      high := mid - 1;
    }
    else
    {
      low := mid + 1;
    }
  }
  return result;
}
// </vc-helpers>

// <vc-spec>
method solve(x: int) returns (result: int)
  requires ValidInput(x)
  ensures IsMinimalTime(result, x)
// </vc-spec>
// <vc-code>
{
  var low := 1;
  var high := x;
  var result := x; // high x is always a valid candidate

  while low <= high
    invariant low >= 1
    invariant high >= 0
    invariant result >= 1
    invariant TriangularNumber(result) >= x
    invariant forall k :: low <= k <= high ==> TriangularNumber(k) >= x ==> result <= k
    invariant forall k :: 1 <= k < low ==> TriangularNumber(k) < x
  {
    var mid := low + (high - low) / 2;
    if TriangularNumber(mid) >= x
    {
      result := mid;
      high := mid - 1;
    }
    else
    {
      low := mid + 1;
    }
  }
  return result;
}
// </vc-code>

