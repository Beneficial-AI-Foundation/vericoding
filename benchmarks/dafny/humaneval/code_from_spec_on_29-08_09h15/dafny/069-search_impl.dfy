

// <vc-helpers>
lemma FreqCount(s: seq<int>, x: int, indices: set<int>)
    requires indices == set i | 0 <= i < |s| && s[i] == x
    ensures |indices| >= 0
{
}

lemma FreqCountUnique(s: seq<int>, x: int, i: int, j: int)
    requires 0 <= i < |s| && 0 <= j < |s|
    requires s[i] == x && s[j] == x
    requires i != j
    ensures i in (set k | 0 <= k < |s| && s[k] == x) && j in (set k | 0 <= k < |s| && s[k] == x)
{
}

lemma SetInvariantHelper(s: seq<int>, x: int, i: int)
    requires 0 <= i < |s|
    ensures (set j | 0 <= j < i && s[j] == x) <= (set j | 0 <= j < i + 1 && s[j] == x)
    ensures if s[i] == x then 
        (set j | 0 <= j < i + 1 && s[j] == x) == (set j | 0 <= j < i && s[j] == x) + {i}
    else 
        (set j | 0 <= j < i + 1 && s[j] == x) == (set j | 0 <= j < i && s[j] == x)
{
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def search(numbers: List[int]) -> int
You are given a non-empty list of positive integers. Return the greatest integer that is greater than zero, and has a frequency greater than or equal to the value of the integer itself. The frequency of an integer is the number of times it appears in the list. If no such a value exist, return -1.
*/
// </vc-description>

// <vc-spec>
method freq(s: seq<int>, x: int) returns (count: int)
    // post-conditions-start
    ensures count == |(set i | 0 <= i < |s| && s[i] == x)|
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    count := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant count == |(set j | 0 <= j < i && s[j] == x)|
    {
        SetInvariantHelper(s, x, i);
        if s[i] == x {
            count := count + 1;
        }
        i := i + 1;
    }
    
    assert (set j | 0 <= j < i && s[j] == x) == (set j | 0 <= j < |s| && s[j] == x);
}
// </vc-code>

