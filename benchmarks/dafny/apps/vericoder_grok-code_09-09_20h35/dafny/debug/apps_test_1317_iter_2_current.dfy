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
// No additional helpers required for this implementation
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
  ghost var counted: set<(int, int)> := {};
  for i := 1 to n
    invariant count == |counted|
    invariant counted == set p : (int, int) | p.0 in 1..(i - 1) && p.1 in 1..n && ((p.0 * p.0 + p.1 * p.1) % m == 0)
  {
    for j := 1 to n
      invariant count == |counted|
      invariant counted == set p : (int, int) | ((p.0 in 1..(i - 1) && p.1 in 1..n) || (p.0 == i && p.1 in 1..(j - 1))) && ((p.0 * p.0 + p.1 * p.1) % m == 0)
    {
      if (i * i + j * j) % m == 0 {
        count := count + 1;
        counted := counted + {(i, j)};
      }
    }
  }
  result := count;
}
// </vc-code>

