

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method sum_to_n(n: int) returns (r : int)
  // post-conditions-start
  ensures r == n * (n + 1) / 2
  // post-conditions-end
// </vc-spec>
// <vc-code>
var s := 0;
var i := 1;
while i <= n
  invariant s == (i-1)*i/2 && 1 <= i <= n+1
{
  s := s + i;
  i := i + 1;
}
r := s;
// </vc-code>

