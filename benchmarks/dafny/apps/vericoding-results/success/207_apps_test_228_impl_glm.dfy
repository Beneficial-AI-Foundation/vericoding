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
lemma MinimumProperty(s: seq<int>)
    requires |s| > 0
    ensures 0 <= countOccurrences(s, minimum(s)) <= |s|
    ensures forall i :: 0 <= i < |s| ==> minimum(s) <= s[i]
    ensures exists i :: 0 <= i < |s| && s[i] == minimum(s)
{
    if |s| == 1 {
    } else {
        MinimumProperty(s[1..]);
        var min_rest := minimum(s[1..]);
        if s[0] <= min_rest {
            assert countOccurrences(s, minimum(s)) == 1 + countOccurrences(s[1..], minimum(s));
        } else {
            assert countOccurrences(s, minimum(s)) == countOccurrences(s[1..], minimum(s));
        }
    }
}

lemma CountNonNegative(s: seq<int>, val: int)
    ensures countOccurrences(s, val) >= 0
{
    if |s| == 0 {
    } else {
        CountNonNegative(s[1..], val);
    }
}

lemma CountLessThanLength(s: seq<int>, val: int)
    ensures countOccurrences(s, val) <= |s|
{
    if |s| == 0 {
    } else {
        CountLessThanLength(s[1..], val);
    }
}

lemma ValidInputImplications(n: int, piles: seq<int>)
    requires ValidInput(n, piles)
    ensures |piles| == n
    ensures |piles| > 0
    ensures n >= 2
    ensures n % 2 == 0
    ensures forall i :: 0 <= i < |piles| ==> piles[i] >= 1
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
    ValidInputImplications(n, piles);
    MinimumProperty(piles);
    CountNonNegative(piles, minimum(piles));
    CountLessThanLength(piles, minimum(piles));
    
    var minVal := minimum(piles);
    var count := countOccurrences(piles, minVal);
    
    if count > n / 2 {
        return "Bob";
    } else {
        return "Alice";
    }
}
// </vc-code>

