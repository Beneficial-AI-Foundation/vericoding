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

  // The range of k for ValidRectangleCorner(k, m, b) is 0 <= k <= b.
  // Since m >= 1, k*m can be large.
  // We need to iterate through all possible valid k values.
  // The maximum value of k is b.
  // Since b <= 10000, this loop is feasible.
  for k := 0 to b
    invariants max_val >= -1
    invariants forall j :: 0 <= j < k ==> max_val >= RectangleValue(j, m, b)
    invariants k <= b + 1
  {
    if ValidRectangleCorner(k, m, b) {
      var current_val := RectangleValue(k, m, b);
      if current_val > max_val {
        max_val := current_val;
      }
    }
  }
  return max_val;
}
// </vc-code>

