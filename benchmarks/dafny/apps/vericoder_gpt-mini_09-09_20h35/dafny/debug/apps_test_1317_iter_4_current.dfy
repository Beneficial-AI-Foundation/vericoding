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
// (no helpers needed)
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int) returns (result: int)
  requires ValidInput(n, m)
  ensures result >= 0
  ensures result == CountCellsDivisibleByM(n, m)
// </vc-spec>
// <vc-code>
{
  result := 0;
  var i := 1;
  while i <= n
    invariant 1 <= i <= n+1
    invariant 0 <= result
    invariant result == |set ii, jj | 1 <= ii <= i-1 && 1 <= jj <= n && (ii*ii + jj*jj) % m == 0 :: (ii, jj)|
  {
    var j := 1;
    while j <= n
      invariant 1 <= i <= n+1
      invariant 1 <= j <= n+1
      invariant 0 <= result
      invariant result == |set ii, jj | ((1 <= ii <= i-1 && 1 <= jj <= n) || (ii == i && 1 <= jj <= j-1)) && (ii*ii + jj*jj) % m == 0 :: (ii, jj)|
    {
      if (i*i + j*j) % m == 0 {
        result := result + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>

