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
function IntMax(a: int, b: int): int
{
  if a > b then a else b
}

function IntMin(a: int, b: int): int
{
  if a < b then a else b
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: int, b: int) returns (result: seq<int>)
  requires ValidInput(n, a, b)
  ensures ValidOutput(result, n, a, b)
// </vc-spec>
// <vc-code>
{
  var x := IntMax(a, b);
  var y := IntMin(a, b);
  var prod_needed := 6 * n;
  var factor1 := x;
  var factor2 := y;
  if (factor1 * factor2 < prod_needed) {
    var ceil_div := (prod_needed + factor1 - 1) / factor1;
    factor2 := IntMax(factor2, ceil_div);
  }
  var product := factor1 * factor2;
  result := [product, factor1, factor2];
}
// </vc-code>

