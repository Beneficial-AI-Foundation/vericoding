

// <vc-helpers>
lemma sum_of_1_to_n(n: int)
  requires n >= 0
  ensures (n * (n + 1) / 2) == sum(n)
{
  if n == 0 {
    assert (0 * (0 + 1) / 2) == 0;
    assert sum(0) == 0;
  } else {
    calc {
      sum(n);
      sum(n-1) + n;
      {(n-1) * ((n-1) + 1) / 2 + n by sum_of_1_to_n(n-1);}
      (n-1) * n / 2 + n;
      (n*n - n + 2*n) / 2;
      (n*n + n) / 2;
      n * (n + 1) / 2;
    }
  }
}

function sum(n: int): int
  requires n >= 0
  decreases n
{
  if n == 0 then 0 else sum(n - 1) + n
}
// </vc-helpers>

// <vc-spec>
method sum_to_n(n: int) returns (r : int)
  // post-conditions-start
  ensures r == n * (n + 1) / 2
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var s := 0;
  while i < n
    invariant 0 <= i <= n
    invariant s == i * (i + 1) / 2
    decreases n - i
  {
    i := i + 1;
    s := s + i;
  }
  return s;
}
// </vc-code>

