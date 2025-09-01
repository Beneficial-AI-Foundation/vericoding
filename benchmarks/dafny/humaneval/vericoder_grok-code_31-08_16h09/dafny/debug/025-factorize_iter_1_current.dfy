function prod(s: seq<int>) : int {
  if |s| == 0 then 1 else prod(s[..|s| - 1]) * s[|s| - 1]
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method factorize(n: nat) returns (factors: seq<nat>)
  // pre-conditions-start
  requires n > 0
  // pre-conditions-end
  // post-conditions-start
  ensures prod(factors) == n
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  factors := [];
  if n == 1 {
    return;
  }
  var i := 2;
  while i * i <= n {
    while n % i == 0 && n > 1 {
      factors := factors + [i];
      n := n / i;
    }
    i := i + 1;
  }
  if n > 1 {
    factors := factors + [n];
  }
}
// </vc-code>

