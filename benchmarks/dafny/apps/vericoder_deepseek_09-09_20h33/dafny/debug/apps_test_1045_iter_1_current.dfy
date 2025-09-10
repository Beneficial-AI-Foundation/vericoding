predicate ValidInput(n: int) {
    n >= 1
}

function CubesForLevel(level: int): int
    requires level >= 1
{
    level * (level + 1) / 2
}

function TotalCubesForHeight(h: int): int
    requires h >= 1
{
    h * (h + 1) * (h + 2) / 6
}

predicate ValidPyramidHeight(n: int, h: int) {
    ValidInput(n) && h >= 1 && 
    TotalCubesForHeight(h) <= n &&
    TotalCubesForHeight(h + 1) > n
}

// <vc-helpers>
lemma BinarySearchLemma(n: int, low: int, high: int)
  requires ValidInput(n)
  requires 1 <= low <= high
  requires TotalCubesForHeight(low) <= n
  requires TotalCubesForHeight(high) > n
  ensures exists h :: low <= h < high && ValidPyramidHeight(n, h)
{
  if high == low + 1 {
    // Base case: exactly one candidate
    assert ValidPyramidHeight(n, low);
  } else {
    var mid := (low + high) / 2;
    if TotalCubesForHeight(mid) <= n {
      BinarySearchLemma(n, mid, high);
    } else {
      BinarySearchLemma(n, low, mid);
    }
  }
}

lemma TotalCubesMonotonic(a: int, b: int)
  requires 1 <= a <= b
  ensures TotalCubesForHeight(a) <= TotalCubesForHeight(b)
{
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result >= 1
    ensures ValidPyramidHeight(n, result)
// </vc-spec>
// <vc-code>
{
  var low := 1;
  var high := n;
  
  while low < high
    invariant 1 <= low <= high <= n
    invariant TotalCubesForHeight(low) <= n
    invariant TotalCubesForHeight(high) > n
  {
    var mid := (low + high) / 2;
    if TotalCubesForHeight(mid) <= n {
      low := mid;
    } else {
      high := mid;
    }
  }
  
  result := low;
  assert ValidPyramidHeight(n, result);
}
// </vc-code>

