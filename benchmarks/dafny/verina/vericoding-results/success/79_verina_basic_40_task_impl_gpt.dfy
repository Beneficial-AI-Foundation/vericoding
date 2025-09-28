// <vc-preamble>
predicate SecondSmallestPrecond(s: array<int>)
    reads s
{
    s.Length > 1
}

predicate SecondSmallestPostcond(s: array<int>, result: int)
    reads s
{
    (exists i :: 0 <= i < s.Length && s[i] == result) &&
    (exists j :: 0 <= j < s.Length && s[j] < result &&
        (forall k :: 0 <= k < s.Length && s[k] != s[j] ==> s[k] >= result))
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): compute minimum of first n elements of s without let-expressions and with explicit decreases */
function MinOfPrefix(s: array<int>, n: nat): int
    requires 1 <= n <= s.Length
    reads s
    decreases n
{
    if n == 1 then s[0]
    else if s[(n as int) - 1] < MinOfPrefix(s, (n - 1) as nat) then s[(n as int) - 1]
    else MinOfPrefix(s, (n - 1) as nat)
}

/* helper modified by LLM (iteration 3): compute second minimum among first n elements given the minimum m (no let, explicit decreases) */
function SecondMinGivenMinOfPrefix(s: array<int>, n: nat, m: int): int
    requires 2 <= n <= s.Length
    requires m == MinOfPrefix(s, n)
    reads s
    decreases n
{
    if n == 2 then
        if s[0] == m then s[1] else s[0]
    else
        if s[(n as int) - 1] == m then
            if MinOfPrefix(s, (n - 1) as nat) == m then
                SecondMinGivenMinOfPrefix(s, (n - 1) as nat, MinOfPrefix(s, (n - 1) as nat))
            else
                MinOfPrefix(s, (n - 1) as nat)
        else
            if SecondMinGivenMinOfPrefix(s, (n - 1) as nat, MinOfPrefix(s, (n - 1) as nat)) <= m then
                s[(n as int) - 1]
            else if s[(n as int) - 1] < SecondMinGivenMinOfPrefix(s, (n - 1) as nat, MinOfPrefix(s, (n - 1) as nat)) then
                s[(n as int) - 1]
            else
                SecondMinGivenMinOfPrefix(s, (n - 1) as nat, MinOfPrefix(s, (n - 1) as nat))
}
// </vc-helpers>

// <vc-spec>
function SecondSmallest(s: array<int>): int
    requires SecondSmallestPrecond(s)
    reads s
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): compute second smallest using helpers */
  SecondMinGivenMinOfPrefix(s, s.Length as nat, MinOfPrefix(s, s.Length as nat))
}
// </vc-code>
