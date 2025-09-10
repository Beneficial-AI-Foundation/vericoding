predicate ValidInput(input: string)
{
    |input| > 0 && '\n' in input &&
    var lines := SplitLinesFunc(input);
    |lines| >= 3 &&
    ValidIntLine(lines[0], 3) &&
    ValidIntLine(lines[1]) &&
    ValidIntLine(lines[2]) &&
    var firstLine := SplitIntsFunc(lines[0]);
    var S := SplitIntsFunc(lines[1]);
    var B := SplitIntsFunc(lines[2]);
    |firstLine| == 3 && firstLine[0] >= 1 && firstLine[1] >= 1 && firstLine[2] >= 1 &&
    |S| == firstLine[0] && |B| == firstLine[1]
}

function ParseInput(input: string): (int, int, int, seq<int>, seq<int>)
    requires ValidInput(input)
    ensures var result := ParseInput(input);
        result.0 >= 1 && result.1 >= 1 && result.2 >= 1 &&
        |result.3| == result.0 && |result.4| == result.1 &&
        (forall i :: 0 <= i < |result.3| ==> result.3[i] >= 1) &&
        (forall i :: 0 <= i < |result.4| ==> result.4[i] >= 1)
{
    var lines := SplitLinesFunc(input);
    var firstLine := SplitIntsFunc(lines[0]);
    var S := SplitIntsFunc(lines[1]);
    var B := SplitIntsFunc(lines[2]);
    (firstLine[0], firstLine[1], firstLine[2], S, B)
}

function ComputeMaxBourles(r: int, S: seq<int>, B: seq<int>): int
    requires r >= 1
    requires |S| >= 1 && |B| >= 1
    requires forall i :: 0 <= i < |S| ==> S[i] >= 1
    requires forall i :: 0 <= i < |B| ==> B[i] >= 1
{
    var x := MinSeqFunc(S);
    var y := MaxSeqFunc(B);
    var cnt := (r % x) + (r / x) * y;
    if r > cnt then r else cnt
}

// <vc-helpers>
lemma MinSeqLemma(s: seq<int>) returns (min: int)
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> s[i] >= 1
    ensures min in s
    ensures forall i :: 0 <= i < |s| ==> min <= s[i]
{
    min := s[0];
    var index := 1;
    while index < |s|
        invariant 1 <= index <= |s|
        invariant min in s[0..index]
        invariant forall i :: 0 <= i < index ==> min <= s[i]
    {
        if s[index] < min {
            min := s[index];
        }
        index := index + 1;
    }
}

lemma MaxSeqLemma(s: seq<int>) returns (max: int)
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> s[i] >= 1
    ensures max in s
    ensures forall i :: 0 <= i < |s| ==> max >= s[i]
{
    max := s[0];
    var index := 1;
    while index < |s|
        invariant 1 <= index <= |s|
        invariant max in s[0..index]
        invariant forall i :: 0 <= i < index ==> max >= s[i]
    {
        if s[index] > max {
            max := s[index];
        }
        index := index + 1;
    }
}

function MinSeqFunc(s: seq<int>): int
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> s[i] >= 1
    ensures result in s
    ensures forall i :: 0 <= i < |s| ==> result <= s[i]
{
    var min := s[0];
    var index := 1;
    while index < |s|
        invariant 1 <= index <= |s|
        invariant min in s[0..index]
        invariant forall i :: 0 <= i < index ==> min <= s[i]
    {
        if s[index] < min {
            min := s[index];
        }
        index := index + 1;
    }
    min
}

function MaxSeqFunc(s: seq<int>): int
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> s[i] >= 1
    ensures result in s
    ensures forall i :: 0 <= i < |s| ==> result >= s[i]
{
    var max := s[0];
    var index := 1;
    while index < |s|
        invariant 1 <= index <= |s|
        invariant max in s[0..index]
        invariant forall i :: 0 <= i < index ==> max >= s[i]
    {
        if s[index] > max {
            max := s[index];
        }
        index := index + 1;
    }
    max
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    requires '\n' in input
    requires ValidInput(input)
    ensures |result| > 0
    ensures exists n, m, r, S, B :: 
        ParseInput(input) == (n, m, r, S, B) &&
        n >= 1 && m >= 1 && r >= 1 &&
        |S| == n && |B| == m &&
        (forall i :: 0 <= i < |S| ==> S[i] >= 1) &&
        (forall i :: 0 <= i < |B| ==> B[i] >= 1) &&
        result == IntToStringFunc(ComputeMaxBourles(r, S, B)) + "\n"
// </vc-spec>
// <vc-code>
{
    var lines := SplitLinesFunc(input);
    var firstLine := SplitIntsFunc(lines[0]);
    var S := SplitIntsFunc(lines[1]);
    var B := SplitIntsFunc(lines[2]);
    var n := firstLine[0];
    var m := firstLine[1];
    var r := firstLine[2];
    
    var x := MinSeqFunc(S);
    var y := MaxSeqFunc(B);
    var cnt := (r % x) + (r / x) * y;
    
    var answer := if r > cnt then r else cnt;
    result := IntToStringFunc(answer) + "\n";
}
// </vc-code>

