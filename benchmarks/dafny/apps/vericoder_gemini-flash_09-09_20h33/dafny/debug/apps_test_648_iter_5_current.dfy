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
function F(k: int, m: int, b: int): int
  requires 0 <= k
  requires 1 <= m
  requires 1 <= b
  requires b - k >= 0
{
  (k * m + 1) * (k * m + b - k) * (k * m + b - k + 1) / 2
}

lemma lemma_f_symmetry(a: int, b: int)
  requires a >= 0 && b >= 0
  ensures f(a, b) == f(b, a)
{
  calc {
    f(a, b);
    (a * (a + 1) * (b + 1) + b * (b + 1) * (a + 1)) / 2;
    ((a * (a + 1) * (b + 1)) + (b * (b + 1) * (a + 1))) / 2;
    ((b * (b + 1) * (a + 1)) + (a * (a + 1) * (b + 1))) / 2;
    f(b, a);
  }
}

lemma lemma_RectangleValue_f_eq(k: int, m: int, b: int)
  requires ValidRectangleCorner(k, m, b)
  requires m >= 1
  ensures RectangleValue(k, m, b) == f(k * m, b - k)
{
  // This lemma is just a direct restatement of the definition,
  // but explicitly stating it can sometimes help the verifier.
}

lemma lemma_max_val_after_loop(m: int, b: int)
  requires ValidInput(m, b)
  ensures exists k_final :: 0 <= k_final <= b && ValidRectangleCorner(k_final, m, b) && RectangleValue(k_final, m, b) >= 0
{
  // Since ValidInput(m, b) implies 1 <= m <= 1000 and 1 <= b <= 10000,
  // we know that k=0 is always a valid rectangle corner (0 <= 0 and b - 0 >= 0).
  // Thus, at least one RectangleValue will be computed and will be a valid integer.
  // The minimum value of f(x,y) for non-negative x,y is 0 (f(0,0)=0).
  // So RectangleValue(k,m,b) will always be non-negative.
  // Therefore, there exists at least one k such that RectangleValue(k,m,b) >= 0.
  assert ValidRectangleCorner(0, m, b);
  assert RectangleValue(0,m,b) >= 0;
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
  var max_val := -1;
  var found_valid_corner := false;

  // The range of k for ValidRectangleCorner(k, m, b) is 0 <= k <= b.
  // Since m >= 1, k*m can be large.
  // We need to iterate through all possible valid k values.
  // The maximum value of k is b.
  // Since b <= 10000, this loop is feasible.
  for k := 0 to b
    invariant -1 <= max_val;
    invariant (found_valid_corner ==> (exists j :: 0 <= j < k && ValidRectangleCorner(j, m, b) && max_val == RectangleValue(j, m, b))) || (!found_valid_corner && max_val == -1);
    invariant forall j :: 0 <= j < k && ValidRectangleCorner(j, m, b) ==> max_val >= RectangleValue(j, m, b);
    invariant found_valid_corner ==> (exists j_found :: 0 <= j_found < k && ValidRectangleCorner(j_found, m, b) && max_val == RectangleValue(j_found, m, b));
    invariant !found_valid_corner ==> max_val == -1;
    invariant (forall j :: 0 <= j < k && ValidRectangleCorner(j, m, b) ==> max_val >= RectangleValue(j,m,b));
  {
    if ValidRectangleCorner(k, m, b) {
      lemma_RectangleValue_f_eq(k, m, b); // Ensure verifier knows the definition
      var current_val := RectangleValue(k, m, b);
      if !found_valid_corner || current_val > max_val {
        max_val := current_val;
        found_valid_corner := true;
      }
    }
  }

  // After the loop, if no valid corner was found, max_val is -1.
  // However, for valid inputs, there must be at least one valid corner (k=0).
  lemma_max_val_after_loop(m, b);
  assert found_valid_corner; // this holds because k=0 is always a valid corner and RectangleValue(0,m,b) is >= 0
  
  return max_val;
}
// </vc-code>

