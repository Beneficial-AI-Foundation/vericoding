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
lemma CountShSubsequencesHelperMonotonic(s: string, index: int, s_count1: int, s_count2: int)
    requires 0 <= index <= |s|
    requires s_count1 >= 0 && s_count2 >= 0
    requires s_count1 <= s_count2
    ensures CountShSubsequencesHelper(s, index, s_count1) <= CountShSubsequencesHelper(s, index, s_count2)
    decreases |s| - index
{
    if index < |s| {
        if s[index] == 's' {
            CountShSubsequencesHelperMonotonic(s, index + 1, s_count1 + 1, s_count2 + 1);
        } else if s[index] == 'h' {
            CountShSubsequencesHelperMonotonic(s, index + 1, s_count1, s_count2);
            assert CountShSubsequencesHelper(s, index, s_count1) == s_count1 + CountShSubsequencesHelper(s, index + 1, s_count1);
            assert CountShSubsequencesHelper(s, index, s_count2) == s_count2 + CountShSubsequencesHelper(s, index + 1, s_count2);
        } else {
            CountShSubsequencesHelperMonotonic(s, index + 1, s_count1, s_count2);
        }
    }
}

lemma CountShSubsequencesAddString(s1: string, s2: string)
    ensures CountShSubsequences(s1 + s2) == 
        CountShSubsequences(s1) + CountShSubsequences(s2) + CountChar(s1, 's') * CountChar(s2, 'h')
{
    calc {
        CountShSubsequencesHelper(s1 + s2, 0, 0);
        CountShSubsequencesHelper(s1, 0, 0) + CountShSubsequences(s2) + (CountChar(s1, 's') + 0) * CountChar(s2, 'h');
        CountShSubsequences(s1) + CountShSubsequences(s2) + CountChar(s1, 's') * CountChar(s2, 'h');
    }
}

lemma CountShSubsequencesConcatenateLemma(s1: string, s2: string, initial_s: int)
    requires initial_s >= 0
    ensures CountShSubsequencesHelper(s1 + s2, 0, initial_s) == 
        CountShSubsequencesHelper(s1, 0, initial_s) + CountShSubsequences(s2) + (CountChar(s1, 's') + initial_s) * CountChar(s2, 'h')
    decreases |s1| + |s2|
{
    if |s1| > 0 {
        var c := s1[0];
        var rest := s1[1..];
        if c == 's' {
            CountShSubsequencesConcatenateLemma(rest, s2, initial_s + 1);
        } else if c == 'h' {
            CountShSubsequencesConcatenateLemma(rest, s2, initial_s);
        } else {
            CountShSubsequencesConcatenateLemma(rest, s2, initial_s);
        }
    } else {
        calc == {
            CountShSubsequencesHelper(s2, 0, initial_s);
            CountShSubsequences(s2) + initial_s * CountChar(s2, 'h');
        }
    }
}

lemma RatioOrderingPreservesCounts(a: string, b: string)
    requires |a| > 0 && |b| > 0
    requires StringRatio(a) <= StringRatio(b)
    ensures CountShSubsequences(a + b) >= CountShSubsequences(b + a)
{
    var s_a := CountChar(a, 's');
    var h_a := CountChar(a, 'h');
    var s_b := CountChar(b, 's');
    var h_b := CountChar(b, 'h');
    
    assert StringRatio(a) <= StringRatio(b) <==> s_a * |b| <= s_b * |a|;
    assert s_a * h_b <= s_b * h_a by {
        if s_a * |b| <= s_b * |a| {
            assert s_a * h_b <= s_b * h_a;
        }
    }
    
    CountShSubsequencesAddString(a, b);
    CountShSubsequencesAddString(b, a);
    
    assert CountShSubsequences(a + b) == CountShSubsequences(a) + CountShSubsequences(b) + s_a * h_b;
    assert CountShSubsequences(b + a) == CountShSubsequences(b) + CountShSubsequences(a) + s_b * h_a;
    
    assert CountShSubsequences(a + b) - CountShSubsequences(b + a) == s_a * h_b - s_b * h_a;
    assert s_a * h_b - s_b * h_a >= 0;
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
    
    var sorted := MergeSort(strings);
    
    var concatenated := ConcatenateStrings(sorted);
    result := CountShSubsequences(concatenated);
}

function MergeSort(strings: seq<string>): seq<string>
    requires forall i :: 0 <= i < |strings| ==> |strings[i]| > 0
    ensures |MergeSort(strings)| == |strings|
    ensures multiset(MergeSort(strings)) == multiset(strings)
    ensures IsSortedByRatio(MergeSort(strings))
{
    if |strings| <= 1 then
        strings
    else
        var mid := |strings| / 2;
        var left := MergeSort(strings[..mid]);
        var right := MergeSort(strings[mid..]);
        Merge(left, right)
}

function Merge(left: seq<string>, right: seq<string>): seq<string>
    requires forall i :: 0 <= i < |left| ==> |left[i]| > 0
    requires forall i :: 0 <= i < |right| ==> |right[i]| > 0
    requires IsSortedByRatio(left) && IsSortedByRatio(right)
    ensures |Merge(left, right)| == |left| + |right|
    ensures multiset(Merge(left, right)) == multiset(left) + multiset(right)
    ensures IsSortedByRatio(Merge(left, right))
    decreases |left| + |right|
{
    if |left| == 0 then
        right
    else if |right| == 0 then
        left
    else if StringRatio(left[0]) <= StringRatio(right[0]) then
        [left[0]] + Merge(left[1..], right)
    else
        [right[0]] + Merge(left, right[1..])
}
// </vc-code>

