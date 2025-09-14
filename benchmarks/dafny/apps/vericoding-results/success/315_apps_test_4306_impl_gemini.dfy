predicate ValidInput(a: int, b: int, c: int, d: int)
{
    0 <= a < b <= 100 && 0 <= c < d <= 100
}

function min(x: int, y: int): int
{
    if x < y then x else y
}

function max(x: int, y: int): int
{
    if x > y then x else y
}

function IntervalOverlapLength(a: int, b: int, c: int, d: int): int
{
    if min(b, d) - max(a, c) > 0 then min(b, d) - max(a, c) else 0
}

// <vc-helpers>
lemma MinLeLe(x: int, y: int, bound: int)
    ensures (x <= bound && y <= bound) ==> min(x, y) <= bound
{
}

lemma MaxGeGe(x: int, y: int, bound: int)
    ensures (x >= bound && y >= bound) ==> max(x, y) >= bound
{
}
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int, c: int, d: int) returns (result: int)
    requires ValidInput(a, b, c, d)
    ensures result >= 0
    ensures result == IntervalOverlapLength(a, b, c, d)
    ensures result <= 100
// </vc-spec>
// <vc-code>
{
  var overlap_len := min(b, d) - max(a, c);
  if overlap_len > 0 {
    result := overlap_len;
  } else {
    result := 0;
  }
}
// </vc-code>

