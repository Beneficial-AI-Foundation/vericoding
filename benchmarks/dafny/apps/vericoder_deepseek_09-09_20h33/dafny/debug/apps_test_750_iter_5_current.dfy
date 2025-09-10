predicate ValidInput(n: int, k: int)
{
  n >= 1 && k >= 1
}

function SheetsNeeded(n: int): (int, int, int)
{
  (2 * n, 5 * n, 8 * n)
}

function TotalSheetsNeeded(n: int): int
{
  2 * n + 5 * n + 8 * n
}

// <vc-helpers>
function CeilDiv(a: int, b: int): int
  requires b > 0
{
  if a <= 0 then 0
  else (a - 1) / b + 1
}

lemma CeilDivLemma(a: int, b: int)
  requires b > 0
  ensures CeilDiv(a, b) == (a + b - 1) / b
{
  if a > 0 {
    var x := (a - 1) / b;
    var y := (a + b - 1) / b;
    calc {
      y;
      ==
      (a + b - 1) / b;
      == { assert (a + b - 1) == b * (y) + ((a + b - 1) % b); }
      if a - 1 < b * (x + 1) then x + 1 else x + 2;
    }
    assert (a - 1) / b == x;
    assert y == x + 1;
  } else {
    assert CeilDiv(a, b) == 0;
    assert (a + b - 1) / b <= (-1 + b - 1) / b;
    assert (a + b - 1) / b <= (b - 2) / b;
    assert (b - 2) / b == 0;
  }
}

lemma CeilDivAddLemma(a: int, b: int, c: int, k: int)
  requires k > 0
  ensures CeilDiv(a, k) + CeilDiv(b, k) + CeilDiv(c, k) >= CeilDiv(a + b + c, k)
{
  var sum := a + b + c;
  assert CeilDiv(sum, k) == if sum <= 0 then 0 else (sum - 1) / k + 1;
  assert CeilDiv(a, k) >= (a) / k;
  assert CeilDiv(b, k) >= (b) / k;
  assert CeilDiv(c, k) >= (c) / k;
  assert CeilDiv(a, k) + CeilDiv(b, k) + CeilDiv(c, k) >= (a + b + c) / k;
  if sum > 0 {
    assert (a + b + c) / k <= CeilDiv(sum, k);
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: int)
  requires ValidInput(n, k)
  ensures result == CeilDiv(2 * n, k) + CeilDiv(5 * n, k) + CeilDiv(8 * n, k)
  ensures result >= 0
  ensures result >= (TotalSheetsNeeded(n) + k - 1) / k
// </vc-spec>
// <vc-code>
{
  var a := 2 * n;
  var b := 5 * n;
  var c := 8 * n;
  result := 0;
  result := result + CeilDiv(a, k);
  result := result + CeilDiv(b, k);
  result := result + CeilDiv(c, k);
}
// </vc-code>

