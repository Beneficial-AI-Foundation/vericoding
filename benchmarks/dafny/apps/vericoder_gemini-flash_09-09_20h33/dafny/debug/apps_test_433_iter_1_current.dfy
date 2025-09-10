predicate ValidInput(n: int, a: int, b: int) {
    n >= 1 && 1 <= a <= n && -100 <= b <= 100
}

function FinalEntrance(n: int, a: int, b: int): int
    requires ValidInput(n, a, b)
{
    ((a - 1 + b) % n + n) % n + 1
}

predicate ValidOutput(result: int, n: int) {
    1 <= result <= n
}

// <vc-helpers>
function Modulo(x: int, n: int): int
  requires n > 0
  ensures 0 <= Modulo(x, n) < n
{
  (x % n + n) % n
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: int, b: int) returns (result: int)
    requires ValidInput(n, a, b)
    ensures ValidOutput(result, n)
    ensures result == FinalEntrance(n, a, b)
// </vc-spec>
// <vc-code>
{
  var temp_b := b;
  if b < 0 {
    temp_b := b % n;
    if temp_b < 0 {
      temp_b := temp_b + n;
    }
  }

  var final_a := (a - 1 + temp_b) % n;
  if final_a < 0 {
    final_a := final_a + n;
  }
  result := final_a + 1;
}
// </vc-code>

