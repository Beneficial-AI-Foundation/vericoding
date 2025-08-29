// <vc-helpers>
function countOccurrences(s: seq<int>, x: int, n: int): int
    requires 0 <= n <= |s|
    decreases n
{
    if n == 0 then 0
    else if s[n-1] == x then 1 + countOccurrences(s, x, n-1)
    else countOccurrences(s, x, n-1)
}

lemma CountOccurrencesCorrect(s: seq<int>, x: int, n: int)
    requires 0 <= n <= |s|
    ensures countOccurrences(s, x, n) == |set i: int | 0 <= i < n && s[i] == x|
    decreases n
{
    if n == 0 {
        assert (set i: int | 0 <= i < n && s[i] == x) == (set {});
        assert |set i: int | 0 <= i < n && s[i] == x| == 0;
    } else {
        CountOccurrencesCorrect(s, x, n-1);
        if s[n-1] == x {
            assert (set i: int | 0 <= i < n && s[i] == x) == (set i: int | 0 <= i < n-1 && s[i] == x) + {n-1};
            assert |set i: int | 0 <= i < n && s[i] == x| == |set i: int | 0 <= i < n-1 && s[i] == x| + 1;
        } else {
            assert (set i: int | 0 <= i < n && s[i] == x) == (set i: int | 0 <= i < n-1 && s[i] == x);
            assert |set i: int | 0 <= i < n && s[i] == x| == |set i: int | 0 <= i < n-1 && s[i] == x|;
        }
    }
}
// </vc-helpers>

// <vc-spec>
method freq(s: seq<int>, x: int) returns (count: int)
    // post-conditions-start
    ensures count == |(set i | 0 <= i < |s| && s[i] == x)|
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    var i := 0;
    count := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant count == countOccurrences(s, x, i)
    {
        if s[i] == x {
            count := count + 1;
        }
        i := i + 1;
    }
    CountOccurrencesCorrect(s, x, |s|);
    assert count == countOccurrences(s, x, |s|);
    assert count == |set i: int | 0 <= i < |s| && s[i] == x|;
}
// </vc-code>
