// <vc-preamble>
function prod(s: seq<int>) : int {
  if |s| == 0 then 1 else prod(s[..|s| - 1]) * s[|s| - 1]
}
// </vc-preamble>

// <vc-helpers>
lemma LemmaProdAppend(s: seq<int>, y: int) 
  ensures prod(s + [y]) == prod(s) * y
{
}
// </vc-helpers>

// <vc-spec>
method factorize(n: nat) returns (factors: seq<nat>)

  requires n > 0

  ensures prod(factors) == n
// </vc-spec>
// <vc-code>
{
  factors := [];
  var rest := n;
  var d: nat := 2;
  while d * d <= rest
    invariant rest > 0
    invariant n == prod(factors) * rest
    decreases rest, n - d
  {
    if rest % d == 0 {
      LemmaProdAppend(factors, d);
      factors := factors + [d];
      rest := rest / d;
    } else {
      d := d + 1;
    }
  }
  if rest > 1 {
    LemmaProdAppend(factors, rest);
    factors := factors + [rest];
  }
}
// </vc-code>
