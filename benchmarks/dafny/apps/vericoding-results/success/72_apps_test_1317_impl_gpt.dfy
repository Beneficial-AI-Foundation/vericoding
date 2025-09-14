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

// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int) returns (result: int)
  requires ValidInput(n, m)
  ensures result >= 0
  ensures result == CountCellsDivisibleByM(n, m)
// </vc-spec>
// <vc-code>
{
  var c := 0;
  ghost var S: set<(int,int)> := {};
  var i := 1;
  while i <= n
    invariant 1 <= i <= n + 1
    invariant S == set ii, jj | 1 <= ii < i && 1 <= jj <= n && (ii * ii + jj * jj) % m == 0 :: (ii, jj)
    invariant c == |S|
    invariant 0 <= c
    decreases n - i + 1
  {
    var j := 1;
    while j <= n
      invariant 1 <= i <= n
      invariant 1 <= j <= n + 1
      invariant S == set ii, jj | 1 <= ii <= i && 1 <= jj <= n && (ii < i || (ii == i && 1 <= jj < j)) && (ii * ii + jj * jj) % m == 0 :: (ii, jj)
      invariant c == |S|
      invariant 0 <= c
      decreases n - j + 1
    {
      if ((i * i + j * j) % m == 0) {
        assert (i, j) !in S;
        S := S + {(i, j)};
        c := c + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  assert S == set ii, jj | 1 <= ii <= n && 1 <= jj <= n && (ii * ii + jj * jj) % m == 0 :: (ii, jj);
  result := c;
}
// </vc-code>

