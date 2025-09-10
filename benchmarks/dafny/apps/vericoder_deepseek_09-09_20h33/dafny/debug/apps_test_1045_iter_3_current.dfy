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
  decreases high - low
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
  if a < b {
    TotalCubesMonotonic(a, b - 1);
    assert TotalCubesForHeight(b - 1) <= TotalCubesForHeight(b);
  }
}

lemma TotalCubesForHeightPositive(h: int)
  requires h >= 1
  ensures TotalCubesForHeight(h) >= 1
{
}
// </vc-helpers>
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
  
  // Initialize the invariant for high
  ghost var h := 1;
  while TotalCubesForHeight(h) <= n && h <= n
    invariant 1 <= h <= n + 1
    invariant TotalCubesForHeight(h) <= n || h == n + 1
  {
    h := h + 1;
  }
  high := h;
  
  while low < high
    invariant 1 <= low <= high <= n + 1
    invariant TotalCubesForHeight(low) <= n
    invariant TotalCubesForHeight(high) > n || high == n + 1
    decreases high - low
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

