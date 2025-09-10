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
function sumDivisibleSubstrings(n: int, p: int, s: string): int
  requires ValidInput(n, p, s)
  ensures sumDivisibleSubstrings(n, p, s) >= 0
  ensures sumDivisibleSubstrings(n, p, s) <= n * (n + 1) / 2
{
  var count := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant count >= 0
    invariant count <= i * (i + 1) / 2
  {
    var j := i;
    while j < n
      invariant i <= j <= n
      invariant count >= 0
      invariant count <= j * (j + 1) / 2
    {
      if substringToInt(s[i..j+1]) % p == 0 then
        count := count + 1;
      j := j + 1;
    }
    i := i + 1;
  }
  return count;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, p: int, s: string) returns (result: int)
    requires ValidInput(n, p, s)
    ensures ValidResult(result, n)
// </vc-spec>
// <vc-code>
{
  return sumDivisibleSubstrings(n, p, s);
}
// </vc-code>

