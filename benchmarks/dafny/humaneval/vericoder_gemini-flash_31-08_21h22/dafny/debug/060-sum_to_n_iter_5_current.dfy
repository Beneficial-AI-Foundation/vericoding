

// <vc-helpers>
lemma sum_of_1_to_n(n: int) returns (s: int)
  requires n >= 0
  ensures s == n * (n + 1) / 2
{
  if n == 0 {
    s := 0;
  } else {
    var prev_s := sum_of_1_to_n(n-1);
    s := prev_s + n;
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
    invariant s == sum(i)
    decreases n - i
  {
    i := i + 1;
    s := s + i;
  }
  return s;
}
// </vc-code>

