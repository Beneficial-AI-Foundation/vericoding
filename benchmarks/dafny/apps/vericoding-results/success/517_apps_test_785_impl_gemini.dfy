predicate ValidInput(n: int, a: int, b: int)
{
  n > 0 && a > 0 && b > 0
}

predicate ValidOutput(result: seq<int>, n: int, a: int, b: int)
{
  |result| == 3 &&
  result[0] >= 6 * n &&
  result[1] > 0 && result[2] > 0 &&
  result[0] == result[1] * result[2] &&
  ((result[1] >= a && result[2] >= b) || (result[1] >= b && result[2] >= a))
}

// <vc-helpers>
lemma Lemma_Ceiling_Mul(n: int, m: int)
  requires n > 0 && m > 0
  ensures m * ((n + m - 1) / m) >= n
{
  var q := (n + m - 1) / m;
  assert n + m - 1 == m * q + (n + m - 1) % m;
  var r := (n + m - 1) % m;
  assert 0 <= r < m;
  
  calc {
    m * q;
    == n + m - 1 - r;
    > n + m - 1 - m; // since r < m
    == n - 1;
  }
  // since m*q and n are integers, m*q > n-1 implies m*q >= n
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: int, b: int) returns (result: seq<int>)
  requires ValidInput(n, a, b)
  ensures ValidOutput(result, n, a, b)
// </vc-spec>
// <vc-code>
{
  var y1 := (6 * n + a - 1) / a;
  Lemma_Ceiling_Mul(6 * n, a);
  var val_y1 := if b > y1 then b else y1;
  var r1_A := a;
  var r2_A := val_y1;
  var area_A := r1_A * r2_A;

  var y2 := (6 * n + b - 1) / b;
  Lemma_Ceiling_Mul(6 * n, b);
  var val_y2 := if a > y2 then a else y2;
  var r1_B := b;
  var r2_B := val_y2;
  var area_B := r1_B * r2_B;

  if area_A <= area_B {
    result := [area_A, r1_A, r2_A];
  } else {
    result := [area_B, r1_B, r2_B];
  }
}
// </vc-code>

