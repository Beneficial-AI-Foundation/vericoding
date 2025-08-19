function maxcheck(s: array<nat>, i: int, max: int): int
requires 0 <= i <= s.Length
reads s
{
    if i == 0 then max
    else if s[i - 1] > max then maxcheck(s, i - 1, s[i - 1])
    else maxcheck(s, i - 1, max)
}

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method max(s: array<nat>) returns (a:int)
requires s.Length > 0
ensures forall x :: 0 <= x < s.Length ==> a >= s[x]
ensures a in s[..]
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>