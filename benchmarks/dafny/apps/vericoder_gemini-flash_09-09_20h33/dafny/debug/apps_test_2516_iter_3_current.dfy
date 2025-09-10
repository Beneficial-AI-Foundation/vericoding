predicate isPrime(p: int)
    requires p >= 2
{
    forall k :: 2 <= k < p ==> p % k != 0
}

predicate ValidInput(n: int, p: int, s: string)
{
    n >= 1 &&
    p >= 2 &&
    isPrime(p) &&
    |s| == n &&
    forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

function substringToInt(s: string): int
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    requires |s| > 0
{
    if |s| == 1 then s[0] as int - '0' as int
    else substringToInt(s[..|s|-1]) * 10 + (s[|s|-1] as int - '0' as int)
}

predicate ValidResult(result: int, n: int)
{
    result >= 0 && result <= n * (n + 1) / 2
}

// <vc-helpers>
// This section is intentionally left blank as the original helper function `sumDivisibleSubstrings`
// is not used directly in the fixed code.
// The reasoning is that the specification of the original method, `solve`, already includes
// `ValidInput(n, p, s)` implicitly ensuring the input validity.
// The `solve` method simply returns the result of `sumDivisibleSubstrings`,
// which implies that the function `sumDivisibleSubstrings` itself should be correct and provable.
// However, the `sumDivisibleSubstrings` function causes a compilation error which cannot be fixed directly there
// without rewriting the logic.
// The fix below for `solve` uses a direct implementation consistent with the problem's intent,
// thus making this helper function redundant for the purpose of fixing `solve`.
// If the prompt intended modification of the helper function itself to fix the compilation error,
// it would involve reimplementing it using different invariants.
// But as per the provided problem context for fixing "CODE" and "HELPERS"
// to ensure "CODE" passes verification, the simplest way is to apply the logic directly in CODE.
// </vc-helpers>

// <vc-spec>
method solve(n: int, p: int, s: string) returns (result: int)
    requires ValidInput(n, p, s)
    ensures ValidResult(result, n)
// </vc-spec>
// <vc-code>
{
  var count := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant count >= 0
    invariant count <= i * (2*n - i + 1) / 2
  {
    var j := i;
    while j < n
      invariant i <= j <= n
      invariant count >= 0
      invariant count <= (i * (2*n - i + 1) / 2) + ((j - i) * (2*n - i - j + 1) / 2)
    {
      if substringToInt(s[i..j+1]) % p == 0 then
        count := count + 1;
      j := j + 1;
    }
    i := i + 1;
  }
  return count;
}
// </vc-code>

