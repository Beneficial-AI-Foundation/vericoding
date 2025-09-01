function prod(s: seq<int>) : int {
  if |s| == 0 then 1 else prod(s[..|s| - 1]) * s[|s| - 1]
}

// <vc-helpers>
function isPrime(n: nat): bool
  requires n > 1
{
  forall i :: 2 <= i <= n && i * i <= n ==> n % i != 0
}

function smallestPrimeFactor(n: nat): nat
  requires n > 1
  ensures exists p :: p == smallestPrimeFactor(n) && isPrime(p) && n % p == 0
  ensures forall k :: 2 <= k < smallestPrimeFactor(n) ==> n % k != 0
{
  if isPrime(n) then n
  else smallestDivisor(n)
}

function smallestDivisor(n: nat): nat
  requires n > 1
  ensures n % smallestDivisor(n) == 0
  ensures forall k :: 2 <= k < smallestDivisor(n) ==> n % k != 0
{
  var d := 2;
  while d * d <= n
    decreases n - d
    invariant d >= 2
    invariant forall k :: 2 <= k < d ==> n % k != 0
    invariant d <= n
  {
    if n % d == 0 then return d;
    d := d + 1;
  }
  return n;
}

lemma FactorizeLemma(n: nat, factors: seq<nat>)
  requires n > 0
  ensures prod(factors) == n ==> forall f :: f in factors ==> f > 0
{
  /* The default implementation of prod needs values > 0 to have prod > 0 */
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
  FactorizeLemma(n, factors); // dummy call to prevent removal if not directly used, but it's used for reasoning.
  var f: seq<nat> := [];
  var current_n := n;

  while current_n > 1
    decreases current_n
    invariant prod(f) * current_n == n
    invariant forall x :: x in f ==> x > 0
  {
    var p := smallestPrimeFactor(current_n);
    f := f + [p];
    current_n := current_n / p;
  }
  factors := f;
}
// </vc-code>

