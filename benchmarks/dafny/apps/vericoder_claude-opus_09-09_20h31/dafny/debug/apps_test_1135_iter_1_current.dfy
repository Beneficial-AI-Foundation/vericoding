predicate ValidInput(n: int, s: string)
{
    n >= 1 && n <= 2000 && |s| == n && 
    forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
}

predicate ValidOutput(result: string, n: int)
{
    |result| == n && 
    forall i :: 0 <= i < |result| ==> 'a' <= result[i] <= 'z'
}

predicate PreservesCharacters(s: string, result: string)
{
    multiset(s) == multiset(result)
}

// <vc-helpers>
lemma SortedPreservesMultiset(s: seq<char>, i: int, j: int)
    requires 0 <= i < j <= |s|
    ensures multiset(s[..i] + [s[j-1]] + s[i..j-1] + s[j..]) == multiset(s)
{
    calc == {
        multiset(s[..i] + [s[j-1]] + s[i..j-1] + s[j..]);
        multiset(s[..i]) + multiset([s[j-1]]) + multiset(s[i..j-1]) + multiset(s[j..]);
        multiset(s[..i]) + multiset([s[j-1]]) + multiset(s[i..j-1]) + multiset(s[j..]);
        { assert s == s[..i] + s[i..j] + s[j..]; }
        { assert s[i..j] == [s[i]] + s[i+1..j] if i < j; }
        { assert s[i..j-1] == s[i..j][..j-1-i]; }
        multiset(s);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, s: string) returns (result: string)
    requires ValidInput(n, s)
    ensures ValidOutput(result, n)
    ensures PreservesCharacters(s, result)
// </vc-spec>
// <vc-code>
{
    var sorted := s;
    var i := 0;
    
    while i < n
        invariant 0 <= i <= n
        invariant |sorted| == n
        invariant forall k :: 0 <= k < |sorted| ==> 'a' <= sorted[k] <= 'z'
        invariant multiset(sorted) == multiset(s)
        invariant forall k1, k2 :: 0 <= k1 < k2 < i ==> sorted[k1] <= sorted[k2]
        invariant forall k1, k2 :: 0 <= k1 < i <= k2 < n ==> sorted[k1] <= sorted[k2]
    {
        var j := i + 1;
        var minIdx := i;
        
        while j < n
            invariant i < j <= n
            invariant i <= minIdx < j
            invariant forall k :: i <= k < j ==> sorted[minIdx] <= sorted[k]
        {
            if sorted[j] < sorted[minIdx] {
                minIdx := j;
            }
            j := j + 1;
        }
        
        if minIdx != i {
            var temp := sorted[i];
            sorted := sorted[i := sorted[minIdx]][minIdx := temp];
        }
        
        i := i + 1;
    }
    
    result := sorted;
}
// </vc-code>

