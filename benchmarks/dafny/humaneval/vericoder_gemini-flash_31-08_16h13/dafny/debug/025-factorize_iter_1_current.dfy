function prod(s: seq<int>) : int {
  if |s| == 0 then 1 else prod(s[..|s| - 1]) * s[|s| - 1]
}

// <vc-helpers>
function isPrime(k: nat): bool
  requires k >= 2
{
  if k==2 then true else
  forall i :: 2 <= i < k ==> k % i != 0
}
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
  if n == 1 {
    return [1];
  }

  var i := 2;
  var tempN := n;
  var currentFactors: seq<nat> := [];

  while i * i <= tempN
    invariant prod(currentFactors) * tempN == n
    invariant forall f | f in currentFactors :: f > 0
    invariant tempN > 0
  {
    if tempN % i == 0 {
      currentFactors := currentFactors + [i];
      tempN := tempN / i;
    } else {
      i := i + 1;
    }
  }

  // After the loop, if tempN > 1, the remaining tempN must be a prime factor
  // (or 1 if the original n was 1, handled above)
  if tempN > 1 {
    currentFactors := currentFactors + [tempN];
  }

  return currentFactors;
}
// </vc-code>

