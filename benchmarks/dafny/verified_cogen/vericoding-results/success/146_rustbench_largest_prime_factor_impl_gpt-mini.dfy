// <vc-preamble>
predicate IsPrimePred(n: int)
{
    forall k :: 2 <= k < n ==> n % k != 0
}
// </vc-preamble>

// <vc-helpers>
function max(a: int, b: int): int { if a >= b then a else b }
lemma DividesOne(n: int) ensures n % 1 == 0 { }
// </vc-helpers>

// <vc-spec>
method LargestPrimeFactor(n: int) returns (result: int)
    requires 2 <= n <= 2147483646
    ensures 1 <= result <= n
    ensures result == 1 || (result > 1 && IsPrimePred(result))
// </vc-spec>
// <vc-code>
{
  var r := 1;
  var i := 2;
  while i <= n
    invariant 2 <= i <= n + 1
    invariant 1 <= r <= n
    invariant r == 1 || IsPrimePred(r)
    invariant n % r == 0
    decreases n - i + 1
  {
    if n % i == 0 {
      if IsPrimePred(i) {
        r := i;
      }
    }
    i := i + 1;
  }
  result := r;
}
// </vc-code>
