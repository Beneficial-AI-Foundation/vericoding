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
lemma ModLemma1(a: int, b: int, d: int)
  requires d > 0 && b > 0
  ensures (a * 10 + b) % d == ((a % d) * 10 + b) % d
{
}

lemma ModLemma2(a: int, b: int, d: int)
  requires d > 0
  ensures (a + b) % d == (a % d + b % d) % d
{
}

lemma PowerLemma(base: int, exponent: int, mod: int)
  requires base >= 0 && exponent >= 0 && mod > 0
  decreases exponent
  ensures mod > 0
{
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, p: int, s: string) returns (result: int)
    requires ValidInput(n, p, s)
    ensures ValidResult(result, n)
// </vc-spec>
// <vc-code>
{
    result := 0;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant 0 <= result <= i * (i + 1) / 2
        decreases n - i
    {
        var current := 0;
        var power := 1;
        var j := i;
        while j < n
            invariant i <= j <= n
            invariant power >= 1
            invariant current >= 0
            decreases n - j
        {
            var digit := s[j] as int - '0' as int;
            current := current * 10 + digit;
            if current % p == 0 {
                result := result + 1;
            }
            j := j + 1;
            power := power * 10;
        }
        i := i + 1;
    }
}
// </vc-code>

