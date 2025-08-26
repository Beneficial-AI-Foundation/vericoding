function maxcheck(s: array<nat>, i: int, max: int): int
requires 0 <= i <= s.Length
reads s
{
    if i == 0 then max
    else if s[i - 1] > max then maxcheck(s, i - 1, s[i - 1])
    else maxcheck(s, i - 1, max)
}

// <vc-helpers>
lemma maxcheck_properties(s: array<nat>, i: int, max: int)
requires 0 <= i <= s.Length
requires max in s[..] || i == 0
ensures maxcheck(s, i, max) in s[..] || (i == 0 && maxcheck(s, i, max) == max)
ensures forall x :: 0 <= x < i ==> maxcheck(s, i, max) >= s[x]
ensures maxcheck(s, i, max) >= max
{
    if i == 0 {
        // Base case
    } else {
        // Recursive case
        if s[i - 1] > max {
            maxcheck_properties(s, i - 1, s[i - 1]);
            assert s[i - 1] in s[..];
        } else {
            maxcheck_properties(s, i - 1, max);
        }
    }
}

lemma maxcheck_in_array(s: array<nat>, i: int, max: int)
requires 0 <= i <= s.Length
requires max in s[..]
ensures maxcheck(s, i, max) in s[..]
{
    maxcheck_properties(s, i, max);
}

lemma maxcheck_covers_all(s: array<nat>, i: int, max: int)
requires 0 <= i <= s.Length
requires max in s[..]
ensures forall x :: 0 <= x < i ==> maxcheck(s, i, max) >= s[x]
ensures forall x :: 0 <= x < s.Length ==> maxcheck(s, s.Length, max) >= s[x]
decreases s.Length - i
{
    maxcheck_properties(s, i, max);
    if i < s.Length {
        maxcheck_covers_all(s, i + 1, max);
    }
}
// </vc-helpers>

// <vc-spec>
method max(s: array<nat>) returns (a:int)
requires s.Length > 0
ensures forall x :: 0 <= x < s.Length ==> a >= s[x]
ensures a in s[..]
// </vc-spec>
// <vc-code>
{
  a := maxcheck(s, s.Length, s[0]);
  assert s[0] in s[..];
  maxcheck_in_array(s, s.Length, s[0]);
  maxcheck_covers_all(s, s.Length, s[0]);
}
// </vc-code>