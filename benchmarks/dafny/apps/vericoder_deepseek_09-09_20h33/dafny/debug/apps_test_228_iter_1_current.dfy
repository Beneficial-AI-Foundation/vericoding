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
lemma minimum_non_negative(s: seq<int>)
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> s[i] >= 1
    ensures minimum(s) >= 1
{
    var m := minimum(s);
    assert exists i :: 0 <= i < |s| && s[i] == m;
}

lemma minimum_monotonic(s: seq<int>, i: int)
    requires 0 <= i < |s|
    ensures minimum(s) <= s[i]
{
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
        return;
    }
    
    var minVal := minimum(piles);
    var count := countOccurrences(piles, minVal);
    
    if count > n / 2 {
        result := "Bob";
    } else {
        result := "Alice";
    }
}
// </vc-code>

