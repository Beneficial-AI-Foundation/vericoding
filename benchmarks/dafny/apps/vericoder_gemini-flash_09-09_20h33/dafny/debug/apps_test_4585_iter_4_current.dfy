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
  var high := x; 
  var result := x; // Initial result can be x, as TriangularNumber(x) >= x for x >= 1

  while low <= high
    invariant low >= 1
    invariant high >= -1 // high can be -1 if mid is 0 and we set high to -1
    invariant result >= 1
    invariant TriangularNumber(result) >= x
    invariant forall k :: high < k <= x ==> TriangularNumber(k) >= x // result is the smallest k in this range
    invariant forall k :: 1 <= k < low ==> TriangularNumber(k) < x 
    invariant low <= x + 1
    invariant result <= x
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
  var result := x; // Initial result can be x, as TriangularNumber(x) >= x for x >= 1

  while low <= high
    invariant low >= 1
    invariant high >= -1 // high can be -1 at the end of the loop
    invariant result >= 1
    invariant TriangularNumber(result) >= x
    invariant forall k :: high < k <= x ==> TriangularNumber(k) >= x // result is the smallest k in this range
    invariant forall k :: 1 <= k < low ==> TriangularNumber(k) < x // All numbers less than low do not satisfy the condition
    invariant low <= x + 1 // loop termination
    invariant result <= x // result is always within a reasonable range
  {
    var mid_val := low + (high - low) / 2;
    // ensure mid_val is non-negative before passing to TriangularNumber
    var mid := if mid_val < 0 then 0 else mid_val; 

    if TriangularNumber(mid) >= x
    {
      result := mid;
      high := mid_val - 1; // Use mid_val here to avoid issues with `mid` being 0
    }
    else
    {
      low := mid_val + 1; // Use mid_val here, as well.
    }
  }
  return result;
}
// </vc-code>

