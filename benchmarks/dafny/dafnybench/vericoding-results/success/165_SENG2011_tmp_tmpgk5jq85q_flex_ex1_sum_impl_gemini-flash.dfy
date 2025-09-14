// sums from index 0 -> i - 1
function sumcheck(s: array<int>, i: int): int
requires 0 <= i <= s.Length
reads s
{
    if i == 0 then 0
    else s[i - 1] + sumcheck(s, i - 1)
}

// returns sum of array

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method sum(s: array<int>) returns (a:int)
requires s.Length > 0
ensures sumcheck(s, s.Length) == a
// </vc-spec>
// <vc-code>
{
    var acc := 0;
    var i := 0;
    while i < s.Length
        invariant 0 <= i <= s.Length
        invariant acc == sumcheck(s, i)
    {
        acc := acc + s[i];
        i := i + 1;
    }
    return acc;
}
// </vc-code>

