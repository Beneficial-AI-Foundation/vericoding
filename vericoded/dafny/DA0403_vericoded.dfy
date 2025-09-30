predicate ValidInput(input: seq<string>)
{
    |input| >= 1 &&
    (forall i :: 0 <= i < |input[0]| ==> '0' <= input[0][i] <= '9') &&
    var n := StringToInt(input[0]);
    n >= 1 && |input| >= n + 1 &&
    forall i :: 1 <= i <= n ==> (|input[i]| > 0 &&
        forall j :: 0 <= j < |input[i]| ==> input[i][j] == 's' || input[i][j] == 'h')
}

function StringToInt(s: string): int
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures StringToInt(s) >= 0
{
    if |s| == 0 then 0
    else StringToInt(s[..|s|-1]) * 10 + (s[|s|-1] as int - '0' as int)
}

function CountChar(s: string, c: char): int
    ensures CountChar(s, c) >= 0
    ensures CountChar(s, c) <= |s|
{
    if |s| == 0 then 0
    else (if s[0] == c then 1 else 0) + CountChar(s[1..], c)
}

function CountShSubsequences(s: string): int
    ensures CountShSubsequences(s) >= 0
{
    CountShSubsequencesHelper(s, 0, 0)
}

function CountShSubsequencesHelper(s: string, index: int, s_count: int): int
    requires 0 <= index <= |s|
    requires s_count >= 0
    ensures CountShSubsequencesHelper(s, index, s_count) >= 0
    decreases |s| - index
{
    if index == |s| then 0
    else if s[index] == 's' then
        CountShSubsequencesHelper(s, index + 1, s_count + 1)
    else if s[index] == 'h' then
        s_count + CountShSubsequencesHelper(s, index + 1, s_count)
    else
        CountShSubsequencesHelper(s, index + 1, s_count)
}

function StringRatio(s: string): real
    requires |s| > 0
{
    (CountChar(s, 's') as real) / (|s| as real)
}

function ConcatenateStrings(strings: seq<string>): string
{
    if |strings| == 0 then ""
    else strings[0] + ConcatenateStrings(strings[1..])
}

predicate IsSortedByRatio(strings: seq<string>)
    requires forall i :: 0 <= i < |strings| ==> |strings[i]| > 0
{
    forall i, j :: 0 <= i < j < |strings| ==> StringRatio(strings[i]) <= StringRatio(strings[j])
}

predicate IsValidArrangement(original: seq<string>, arranged: seq<string>)
{
    |arranged| == |original| && multiset(arranged) == multiset(original)
}

// <vc-helpers>
lemma StringToIntNonNegative(s: string)
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures StringToInt(s) >= 0
{
    // This follows from the ensures clause of StringToInt
}

lemma CountShSubsequencesNonNegative(s: string)
    ensures CountShSubsequences(s) >= 0
{
    // This follows from the ensures clause of CountShSubsequences
}

lemma ConcatenateStringsAppend(strings: seq<string>, idx: int)
    requires 0 <= idx < |strings|
    ensures ConcatenateStrings(strings[..idx+1]) == ConcatenateStrings(strings[..idx]) + strings[idx]
{
    var prefix := strings[..idx+1];
    var prefixMinusOne := strings[..idx];
    
    if idx == 0 {
        assert prefix == [strings[0]];
        assert prefixMinusOne == [];
        assert ConcatenateStrings(prefix) == strings[0] + ConcatenateStrings([]);
        assert ConcatenateStrings([]) == "";
        assert ConcatenateStrings(prefix) == strings[0];
        assert ConcatenateStrings(prefixMinusOne) == "";
    } else {
        // For idx > 0, we need to reason about the recursive structure
        assert prefix == prefixMinusOne + [strings[idx]];
        ConcatenateStringsDistributive(prefixMinusOne, [strings[idx]]);
    }
}

lemma ConcatenateStringsDistributive(s1: seq<string>, s2: seq<string>)
    ensures ConcatenateStrings(s1 + s2) == ConcatenateStrings(s1) + ConcatenateStrings(s2)
{
    if |s1| == 0 {
        assert s1 + s2 == s2;
        assert ConcatenateStrings(s1) == "";
    } else {
        assert (s1 + s2)[0] == s1[0];
        assert (s1 + s2)[1..] == s1[1..] + s2;
        ConcatenateStringsDistributive(s1[1..], s2);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(input: seq<string>) returns (result: int)
    requires ValidInput(input)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
    var n := StringToInt(input[0]);
    var strings := input[1..n+1];
    
    // Sort strings by ratio of 's' characters (ascending)
    var sorted := strings;
    var i := 0;
    while i < |sorted|
        invariant 0 <= i <= |sorted|
        invariant |sorted| == |strings|
        invariant multiset(sorted) == multiset(strings)
        invariant forall k :: 0 <= k < |sorted| ==> |sorted[k]| > 0
        invariant forall j :: 0 <= j < i ==> forall k :: j < k < |sorted| ==> StringRatio(sorted[j]) <= StringRatio(sorted[k])
        invariant forall j, k :: 0 <= j < k < i ==> StringRatio(sorted[j]) <= StringRatio(sorted[k])
    {
        var j := i;
        var minIdx := i;
        var minRatio := StringRatio(sorted[i]);
        
        while j < |sorted|
            invariant i <= j <= |sorted|
            invariant i <= minIdx < |sorted|
            invariant minRatio == StringRatio(sorted[minIdx])
            invariant forall k :: i <= k < j ==> StringRatio(sorted[minIdx]) <= StringRatio(sorted[k])
        {
            if StringRatio(sorted[j]) < minRatio {
                minIdx := j;
                minRatio := StringRatio(sorted[j]);
            }
            j := j + 1;
        }
        
        // After finding minimum, swap if needed
        if minIdx != i {
            var temp := sorted[i];
            var newSorted := sorted[i := sorted[minIdx]][minIdx := temp];
            
            // Assert that the swap maintains the invariants
            assert multiset(newSorted) == multiset(sorted);
            assert |newSorted| == |sorted|;
            assert forall k :: 0 <= k < |newSorted| ==> |newSorted[k]| > 0;
            assert newSorted[i] == sorted[minIdx];
            assert forall k :: i < k < |sorted| ==> StringRatio(newSorted[i]) <= StringRatio(newSorted[k]);
            
            sorted := newSorted;
        }
        
        i := i + 1;
    }
    
    // Concatenate all sorted strings
    var concatenated := "";
    var idx := 0;
    while idx < |sorted|
        invariant 0 <= idx <= |sorted|
        invariant concatenated == ConcatenateStrings(sorted[..idx])
    {
        ConcatenateStringsAppend(sorted, idx);
        concatenated := concatenated + sorted[idx];
        idx := idx + 1;
    }
    
    // Count sh subsequences in the concatenated string
    result := CountShSubsequences(concatenated);
}
// </vc-code>

