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
  requires a >= 0 && b > 0
{
  (a + b - 1) / b
}

lemma CeilDivUpperBound(a: int, d: int)
  requires a >= 0 && d > 0
  ensures a <= d * CeilDiv(a, d)
{
  var ca := CeilDiv(a, d);
  var r := (a + d - 1) % d;
  calc {
    d * ca;
    == d * ((a + d - 1) / d);
    == (a + d - 1) - r;
    >= (a + d - 1) - (d - 1);
    == a;
  }
}

lemma DivPlus(y: int, k: int, d: int)
  requires d > 0
  ensures (d*y + k)/d == y + k/d
{
    var r := k % d;
    calc {
        (d*y+k)/d;
        == (d*y + (k/d)*d + r)/d;
        == ((y + k/d)*d + r)/d;
        == y + k/d;
    }
}

lemma CeilDivSum(a: int, b: int, d: int)
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: int)
  requires ValidInput(n, k)
  ensures result == CeilDiv(2 * n, k) + CeilDiv(5 * n, k) + CeilDiv(8 * n, k)
  ensures result >= 0
  ensures result >= (TotalSheetsNeeded(n) + k - 1) / k
// </vc-spec>
// <vc-code>
function CeilDiv(a: int, b: int): int
  requires a >= 0 && b > 0
{
  (a + b - 1) / b
}

lemma CeilDivUpperBound(a: int, d: int)
  requires a >= 0 && d > 0
  ensures a <= d * CeilDiv(a, d)
{
  var ca := CeilDiv(a, d);
  var r := (a + d - 1) % d;
  calc {
    d * ca;
    == d * ((a + d - 1) / d);
    == (a + d - 1) - r;
    >= (a + d - 1) - (d - 1);
    == a;
  }
}

lemma DivPlus(y: int, k: int, d: int)
  requires d > 0
  ensures (d*y + k)/d == y + k/d
{
    var r := k % d;
    calc {
        (d*y+k)/d;
        == (d*y + (k/d)*d + r)/d;
        == ((y + k/d)*d + r)/d;
        == y + k/d;
    }
}

lemma CeilDivSum(a: int, b: int, d: int)
// </vc-code>

