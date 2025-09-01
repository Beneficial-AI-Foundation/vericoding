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
  var working_n := n;
  var i := 2;
  while i * i <= working_n
    invariant 2 <= i
    invariant n == prod(factors) * working_n
    decreases working_n - i + 1
  {
    while working_n % i == 0 && working_n > 1 {
      factors := factors + [i];
      working_n := working_n / i;
    }
    i := i + 1;
  }
  if working_n > 1 {
    factors := factors + [working_n];
  }
}
// </vc-code>

