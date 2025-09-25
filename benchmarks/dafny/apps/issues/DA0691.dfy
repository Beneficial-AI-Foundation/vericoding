// <vc-preamble>
predicate ValidInput(n: int, a: int, b: int, c: int)
{
  n >= 1 && a >= 1 && b >= 1 && c >= 1 && c < b &&
  n <= 1000000000000000000 && a <= 1000000000000000000 && 
  b <= 1000000000000000000
}

function MaxLiters(n: int, a: int, b: int, c: int): int
  requires ValidInput(n, a, b, c)
{
  if n <= c then n / a else 
    max(max(n / a, (n / a - b + c) / a + 1), 
        (n - c) / (b - c) + ((n - c) % (b - c) + c) / a)
}

function max(x: int, y: int): int
{
  if x >= y then x else y
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: int, b: int, c: int) returns (result: int)
  requires ValidInput(n, a, b, c)
  ensures result >= 0
  ensures result <= n / a
  ensures result == MaxLiters(n, a, b, c)
// </vc-spec>
// <vc-code>
{
  var r := n / a;
  if n > c {
    var option1 := r;
    var option2 := (r - b + c) / a + 1;
    var option3 := (n - c) / (b - c) + ((n - c) % (b - c) + c) / a;

    r := option1;
    if option2 > r {
      r := option2;
    }
    if option3 > r {
      r := option3;
    }
  }
  result := r;
}
// </vc-code>
