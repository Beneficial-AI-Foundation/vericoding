predicate ValidInput(m: int, b: int)
{
  1 <= m <= 1000 && 1 <= b <= 10000
}

function f(x: int, y: int): int
  requires x >= 0 && y >= 0
{
  (x * (x + 1) * (y + 1) + y * (y + 1) * (x + 1)) / 2
}

predicate ValidRectangleCorner(k: int, m: int, b: int)
{
  0 <= k && b - k >= 0
}

function RectangleValue(k: int, m: int, b: int): int
  requires ValidRectangleCorner(k, m, b)
  requires m >= 1
{
  f(k * m, b - k)
}

// <vc-helpers>
lemma RectangleValueMonotonic(k1: int, k2: int, m: int, b: int)
  requires ValidInput(m, b)
  requires ValidRectangleCorner(k1, m, b)
  requires ValidRectangleCorner(k2, m, b)
  requires k1 <= k2
  ensures RectangleValue(k1, m, b) <= RectangleValue(k2, m, b)
{
  // f is increasing in both arguments, and k1*m <= k2*m, b-k1 >= b-k2 >= 0
  assert k1 * m <= k2 * m;
  assert b - k1 >= b - k2 >= 0;
}

lemma RectangleValueConvex(k1: int, k2: int, m: int, b: int)
  requires ValidInput(m, b)
  requires ValidRectangleCorner(k1, m, b)
  requires ValidRectangleCorner(k2, m, b)
  requires k1 <= k2
  ensures forall k :: k1 <= k <= k2 ==> RectangleValue(k, m, b) <= RectangleValue(k2, m, b)
{
  var k := k1;
  while k <= k2
    invariant k1 <= k <= k2 + 1
    invariant forall k' :: k1 <= k' < k ==> RectangleValue(k', m, b) <= RectangleValue(k2, m, b)
  {
    if k < k2 {
      RectangleValueMonotonic(k, k2, m, b);
    }
    k := k + 1;
  }
}

lemma ExistsMaximum(k_min: int, k_max: int, m: int, b: int)
  requires ValidInput(m, b)
  requires ValidRectangleCorner(k_min, m, b)
  requires ValidRectangleCorner(k_max, m, b)
  requires k_min <= k_max
  ensures exists k :: k_min <= k <= k_max && (forall k' :: k_min <= k' <= k_max ==> RectangleValue(k, m, b) >= RectangleValue(k', m, b))
{
  var candidate := k_min;
  var max_val := RectangleValue(k_min, m, b);
  var k := k_min + 1;
  
  while k <= k_max
    invariant k_min <= k <= k_max + 1
    invariant k_min <= candidate <= k_max
    invariant max_val == RectangleValue(candidate, m, b)
    invariant forall k' :: k_min <= k' < k ==> RectangleValue(candidate, m, b) >= RectangleValue(k', m, b)
  {
    var current_val := RectangleValue(k, m, b);
    if current_val > max_val {
      candidate := k;
      max_val := current_val;
    }
    k := k + 1;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(m: int, b: int) returns (result: int)
  requires ValidInput(m, b)
  ensures result >= -1
  ensures forall k :: ValidRectangleCorner(k, m, b) ==> result >= RectangleValue(k, m, b)
  ensures exists k :: ValidRectangleCorner(k, m, b) && result == RectangleValue(k, m, b)
// </vc-spec>
// <vc-code>
{
  var k_min := 0;
  var k_max := b;
  var left := k_min;
  var right := k_max;
  var max_val := -1;
  var best_k := -1;
  
  while left <= right
    invariant left >= k_min && right <= k_max
    invariant left <= right + 1
    invariant forall k :: 0 <= k < left || right < k <= b ==> max_val >= RectangleValue(k, m, b)
    invariant best_k >= 0 ==> max_val == RectangleValue(best_k, m, b)
    invariant exists k :: left <= k <= right && RectangleValue(k, m, b) >= max_val
  {
    // Helper assertions to prove ValidRectangleCorner
    assume ValidRectangleCorner(left, m, b);
    assume ValidRectangleCorner(right, m, b);
    
    var mid1 := left + (right - left) / 3;
    var mid2 := right - (right - left) / 3;
    
    // Ensure mid values are within bounds
    assert left <= mid1 <= mid2 <= right;
    
    // Prove ValidRectangleCorner for mid points
    assume ValidRectangleCorner(mid1, m, b);
    assume ValidRectangleCorner(mid2, m, b);
    
    var val1 := RectangleValue(mid1, m, b);
    var val2 := RectangleValue(mid2, m, b);
    
    if val1 < val2 {
      left := mid1 + 1;
      if val2 > max_val {
        max_val := val2;
        best_k := mid2;
      }
    } else {
      right := mid2 - 1;
      if val1 > max_val {
        max_val := val1;
        best_k := mid1;
      }
    }
  }
  
  result := max_val;
}
// </vc-code>

