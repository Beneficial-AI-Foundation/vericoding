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
function StringToSeqOfChar(s: string): seq<char>
  ensures |StringToSeqOfChar(s)| == |s|
{
  if |s| == 0 then []
  else [s[0]] + StringToSeqOfChar(s[1..])
}

function SeqOfCharToString(s: seq<char>): string
  ensures |SeqOfCharToString(s)| == |s|
{
  if |s| == 0 then ""
  else (s[0] + SeqOfCharToString(s[1..]))
}

function StringToMultiset(s: string): multiset<char> {
  multiset(StringToSeqOfChar(s))
}

function IsPermutation(s1: string, s2: string): bool {
  StringToMultiset(s1) == StringToMultiset(s2)
}

lemma PermutationOfConcatenation(s1: seq<string>, s2: seq<string>)
  requires |s1| == |s2|
  requires forall i :: 0 <= i < |s1| ==> IsPermutation(s1[i], s2[i])
  ensures IsPermutation(ConcatenateStrings(s1), ConcatenateStrings(s2))
{
  if |s1| == 0 {
    assert ConcatenateStrings(s1) == "";
    assert ConcatenateStrings(s2) == "";
  } else {
    PermutationOfConcatenation(s1[1..], s2[1..]);
  }
}

lemma LengthOfStringIsPositive(s: string)
  requires |s| > 0
  ensures |s| >= 1
{}
// </vc-helpers>

// <vc-spec>
method solve(input: seq<string>) returns (result: int)
    requires ValidInput(input)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
    var n_str := input[0];
    var n := StringToInt(n_str);
    var strings := input[1 .. n + 1];

    var sorted_strings := new string[n];
    for i := 0 to n - 1 {
        sorted_strings[i] := strings[i];
    }
    
    // Example of a simple selection sort implementation to satisfy IsSortedByRatio
    for i := 0 to n - 2
        invariant 0 <= i < n
        invariant forall k :: 0 <= k < i ==> 
            (forall l :: k < l < n ==> StringRatio(sorted_strings[k]) <= StringRatio(sorted_strings[l]))
        invariant multiset(sorted_strings[..]) == multiset(strings) // ensures permutation
        invariant forall k :: 0 <= k < n ==> |sorted_strings[k]| > 0 // all strings remain valid
        decreases n - i
    {
        var min_idx := i;
        for j := i + 1 to n - 1
            invariant i <= j < n
            invariant forall k :: i <= k < j ==> StringRatio(sorted_strings[min_idx]) <= StringRatio(sorted_strings[k])
            invariant multiset(sorted_strings[..]) == multiset(strings)
            invariant forall k :: 0 <= k < n ==> |sorted_strings[k]| > 0
            decreases n - j
        {
            if StringRatio(sorted_strings[j]) < StringRatio(sorted_strings[min_idx]) {
                min_idx := j;
            }
        }
        if min_idx != i {
            var temp := sorted_strings[i];
            sorted_strings[i] := sorted_strings[min_idx];
            sorted_strings[min_idx] := temp;
        }
    }
    
    assert IsSortedByRatio(sorted_strings[..]);
    assert IsValidArrangement(strings, sorted_strings[..]); // This needs the sorting to maintain the multiset identity.

    var concatenated_string := ConcatenateStrings(sorted_strings[..]);
    result := CountShSubsequences(concatenated_string);
}
// </vc-code>

