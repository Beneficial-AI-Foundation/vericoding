// <vc-preamble>
function prod(s: seq<int>) : int {
  if |s| == 0 then 1 else prod(s[..|s| - 1]) * s[|s| - 1]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fixed division by zero and postcondition issues */
function is_factor(a: nat, b: nat): bool
  requires b > 0
  requires a > 0
{
  b % a == 0
}

function smallest_factor(n: nat): nat
  requires n > 1
  ensures smallest_factor(n) > 1
  ensures smallest_factor(n) <= n
  ensures is_factor(smallest_factor(n), n)
{
  smallest_factor_helper(n, 2)
}

function smallest_factor_helper(n: nat, candidate: nat): nat
  requires n > 1
  requires candidate >= 2
  requires candidate <= n
  ensures smallest_factor_helper(n, candidate) >= candidate
  ensures smallest_factor_helper(n, candidate) <= n
  ensures is_factor(smallest_factor_helper(n, candidate), n)
  decreases n - candidate + 1
{
  if candidate == n then n
  else if n % candidate == 0 then candidate
  else smallest_factor_helper(n, candidate + 1)
}

lemma prod_append_one(s: seq<int>, x: int)
  ensures prod(s + [x]) == prod(s) * x
{
  if |s| == 0 {
    assert prod(s + [x]) == prod([x]) == x;
    assert prod(s) * x == 1 * x == x;
  } else {
    assert (s + [x])[..|s + [x]| - 1] == s;
    assert (s + [x])[|s + [x]| - 1] == x;
  }
}
// </vc-helpers>

// <vc-spec>
method factorize(n: nat) returns (factors: seq<nat>)

  requires n > 0

  ensures prod(factors) == n
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): simplified factorization logic */
  factors := [];
  var remaining := n;
  
  while remaining > 1
    invariant remaining >= 1
    invariant prod(factors) * remaining == n
    decreases remaining
  {
    var factor := smallest_factor(remaining);
    factors := factors + [factor];
    remaining := remaining / factor;
    
    prod_append_one(factors[..|factors|-1], factor);
  }
}
// </vc-code>
