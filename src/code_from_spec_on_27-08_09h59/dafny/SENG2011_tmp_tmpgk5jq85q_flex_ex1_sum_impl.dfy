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
lemma SumcheckIncremental(s: array<int>, i: int)
    requires 0 <= i < s.Length
    ensures sumcheck(s, i + 1) == sumcheck(s, i) + s[i]
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method sum(s: array<int>) returns (a:int)
requires s.Length > 0
ensures sumcheck(s, s.Length) == a
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    var i := 0;
    a := 0;
    
    while i < s.Length
        invariant 0 <= i <= s.Length
        invariant a == sumcheck(s, i)
    {
        SumcheckIncremental(s, i);
        a := a + s[i];
        i := i + 1;
    }
}
// </vc-code>
