// <vc-preamble>
predicate Is2Pow( n: int )
    decreases n;
{
    if n < 1 then
        false
    else if n == 1 then
        true
    else
        n%2 == 0 && Is2Pow(n/2)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simplified lemma to have an empty body as the proof is trivial for Dafny */
lemma Is2PowRecursiveStep(n: int)
    requires n > 0 && Is2Pow(n+1)
    ensures Is2Pow(((n-1)/2) + 1)
{ 
}
// </vc-helpers>

// <vc-spec>
method Search2PowRecursive( a: array<int>, i: int, n: int, x: int ) returns ( k: int )
    decreases n;
    requires 0 <= i <= i+n <= a.Length;
    requires forall p,q | i <= p < q < i+n :: a[p] <= a[q];
    requires Is2Pow(n+1);
    ensures i <= k <= i+n;
    ensures forall r | i <= r < k :: a[r] < x;
    ensures forall r | k <= r < i+n :: a[r] >= x;
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): resubmitting correct code from previous turn */
{
  if n == 0 {
    k := i;
  } else {
    var m := (n - 1) / 2;
    var j := i + m;

    Is2PowRecursiveStep(n);

    if a[j] < x {
      k := Search2PowRecursive(a, j + 1, m, x);
    } else {
      k := Search2PowRecursive(a, i, m, x);
    }
  }
}
// </vc-code>
