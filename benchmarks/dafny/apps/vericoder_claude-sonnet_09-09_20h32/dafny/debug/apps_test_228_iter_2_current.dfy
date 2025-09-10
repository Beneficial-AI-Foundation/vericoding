function minimum(s: seq<int>): int
    requires |s| > 0
    ensures forall i :: 0 <= i < |s| ==> minimum(s) <= s[i]
    ensures exists i :: 0 <= i < |s| && s[i] == minimum(s)
{
    if |s| == 1 then s[0]
    else if s[0] <= minimum(s[1..]) then s[0]
    else minimum(s[1..])
}

function countOccurrences(s: seq<int>, val: int): int
    ensures countOccurrences(s, val) >= 0
    ensures countOccurrences(s, val) <= |s|
{
    if |s| == 0 then 0
    else (if s[0] == val then 1 else 0) + countOccurrences(s[1..], val)
}

predicate ValidInput(n: int, piles: seq<int>)
{
    n >= 2 && n % 2 == 0 && |piles| == n && forall i :: 0 <= i < |piles| ==> piles[i] >= 1
}

// <vc-helpers>
lemma MinimumExists(s: seq<int>)
    requires |s| > 0
    ensures exists i :: 0 <= i < |s| && s[i] == minimum(s)
{
    if |s| == 1 {
        assert s[0] == minimum(s);
    } else {
        var min_tail := minimum(s[1..]);
        MinimumExists(s[1..]);
        if s[0] <= min_tail {
            assert s[0] == minimum(s);
        } else {
            assert min_tail == minimum(s);
            var j :| 1 <= j < |s| && s[j] == min_tail;
            assert s[j] == minimum(s);
        }
    }
}

lemma CountOccurrencesCorrect(s: seq<int>, val: int)
    ensures countOccurrences(s, val) == |set i | 0 <= i < |s| && s[i] == val|
{
    if |s| == 0 {
        assert set i | 0 <= i < |s| && s[i] == val == {};
    } else {
        CountOccurrencesCorrect(s[1..], val);
        var tail_set := set i | 0 <= i < |s[1..]| && s[1..][i] == val;
        var full_set := set i | 0 <= i < |s| && s[i] == val;
        var shifted_tail_set := set i | 1 <= i < |s| && s[i] == val;
        
        assert tail_set == shifted_tail_set;
        
        if s[0] == val {
            assert full_set == {0} + shifted_tail_set;
            assert 0 !in shifted_tail_set;
            assert |full_set| == 1 + |shifted_tail_set|;
        } else {
            assert full_set == shifted_tail_set;
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, piles: seq<int>) returns (result: string)
    requires ValidInput(n, piles)
    ensures result == "Alice" || result == "Bob"
    ensures |piles| > 0 ==> 
        (var minVal := minimum(piles);
         var count := countOccurrences(piles, minVal);
         result == (if count > n / 2 then "Bob" else "Alice"))
    ensures |piles| == 0 ==> result == "Alice"
// </vc-spec>
// <vc-code>
{
    if |piles| == 0 {
        result := "Alice";
    } else {
        MinimumExists(piles);
        var minVal := minimum(piles);
        CountOccurrencesCorrect(piles, minVal);
        var count := countOccurrences(piles, minVal);
        if count > n / 2 {
            result := "Bob";
        } else {
            result := "Alice";
        }
    }
}
// </vc-code>

