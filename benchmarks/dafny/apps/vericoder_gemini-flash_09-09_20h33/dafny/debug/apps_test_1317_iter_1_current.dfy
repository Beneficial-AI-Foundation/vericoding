function CountCellsDivisibleByM(n: int, m: int): int
  requires 1 <= n
  requires 1 <= m
{
  |set i, j | 1 <= i <= n && 1 <= j <= n && (i * i + j * j) % m == 0 :: (i, j)|
}

predicate ValidInput(n: int, m: int) {
  1 <= n && 1 <= m <= 1000
}

// <vc-helpers>
/**
 * `key % m == 0` is equivalent to `key - m * (key / m) == 0`, which simplifies to `key == m * (key / m)`.
 * This means `key` is a multiple of `m`.
 */
function IsDivisible(key: int, m: int): bool
  requires m > 0
{
  key % m == 0
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int) returns (result: int)
  requires ValidInput(n, m)
  ensures result >= 0
  ensures result == CountCellsDivisibleByM(n, m)
// </vc-spec>
// <vc-code>
{
  var count := 0;
  for i := 1 to n
    invariant 0 <= i <= n + 1
    invariant count == CountCellsDivisibleByM(i - 1, m)
  {
    for j := 1 to n
      invariant 0 <= j <= n + 1
      invariant count == CountCellsDivisibleByM(i - 1, m) + (if i <= n then CountCellsDivisibleByMOneRow(i, j - 1, n, m) else 0)
    {
      if IsDivisible(i * i + j * j, m) {
        count := count + 1;
      }
    }
  }
  result := count;
}

function CountCellsDivisibleByMOneRow(targetI: int, jMax: int, n: int, m: int): int
  requires 1 <= targetI <= n
  requires 0 <= jMax <= n
  requires 1 <= m
{
  |set j | 1 <= j <= jMax && (targetI * targetI + j * j) % m == 0 :: (targetI, j)|
}
// </vc-code>

