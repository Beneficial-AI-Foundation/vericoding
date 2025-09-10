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
  ghost var S: set<(int, int)> := {};
  var count := 0;
  for i := 1 to n
    invariant count == |set (x,y) | 1<=x<=i-1 && 1<=y<=n && (x*x+y*y)%m==0|
    invariant S == set (x,y) | 1<=x<=i-1 && 1<=y<=n && (x*x+y*y)%m==0
  {
    for j := 1 to n
      invariant count == |set (x,y) | (1<=x<=i-1 && 1<=y<=n && (x*x+y*y)%m==0) || (x==i && 1<=y<=j-1 && (i*i+y*y)%m==0)|
      invariant S == set (x,y) | (1<=x<=i-1 && 1<=y<=n && (x*x+y*y)%m==0) || (x==i && 1<=y<=j-1 && (i*i+y*y)%m==0)
    {
      if (i*i + j*j) % m == 0 then
        count := count + 1;
        S := S + {(i, j)};
    }
  }
  result := count;
}
// </vc-code>

