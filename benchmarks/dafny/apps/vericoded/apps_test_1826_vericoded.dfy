predicate ValidInput(input: string)
{
    |input| > 0 && exists pos :: 0 <= pos < |input| && input[pos] == '\n'
}

predicate ValidMoveSequence(s: string)
{
    forall i :: 0 <= i < |s| ==> s[i] == 'U' || s[i] == 'R'
}

function CountReplacements(s: string, start: int, length: int): int
    requires 0 <= start <= |s|
    requires length >= 0
    requires start + length <= |s|
    ensures CountReplacements(s, start, length) >= 0
    ensures CountReplacements(s, start, length) <= length / 2
{
    if length <= 1 then 0
    else CountReplacementsHelper(s, start, length, 1, 0)
}

function CountReplacementsHelper(s: string, start: int, length: int, i: int, count: int): int
    requires 0 <= start <= |s|
    requires length >= 0
    requires start + length <= |s|
    requires 1 <= i <= length
    requires count >= 0
    requires count <= (i - 1) / 2
    ensures CountReplacementsHelper(s, start, length, i, count) >= count
    ensures CountReplacementsHelper(s, start, length, i, count) <= length / 2
    decreases length - i
{
    if i >= length then count
    else if start + i < |s| && s[start + i - 1] != s[start + i] then
        if i + 2 <= length then CountReplacementsHelper(s, start, length, i + 2, count + 1)
        else count + 1
    else
        CountReplacementsHelper(s, start, length, i + 1, count)
}

function MinimizedLength(originalLength: int, replacements: int): int
    requires originalLength >= 0
    requires replacements >= 0
    requires replacements <= originalLength / 2
{
    originalLength - replacements
}

// <vc-helpers>
method ParseInput(input: string) returns (n: int, s: string)
    requires ValidInput(input)
    ensures n >= 0
    ensures |s| == n
    ensures ValidMoveSequence(s)
{
    var newlinePos := 0;
    while newlinePos < |input| && input[newlinePos] != '\n'
        invariant 0 <= newlinePos <= |input|
        invariant forall i :: 0 <= i < newlinePos ==> input[i] != '\n'
    {
        newlinePos := newlinePos + 1;
    }
    
    n := 0;
    var i := 0;
    while i < newlinePos
        invariant 0 <= i <= newlinePos
        invariant n >= 0
    {
        if '0' <= input[i] <= '9' {
            n := n * 10 + (input[i] as int - '0' as int);
        }
        i := i + 1;
    }
    
    s := "";
    i := newlinePos + 1;
    while i < |input| && |s| < n
        invariant newlinePos + 1 <= i <= |input|
        invariant 0 <= |s| <= n
        invariant ValidMoveSequence(s)
    {
        if input[i] == 'U' || input[i] == 'R' {
            s := s + [input[i]];
        }
        i := i + 1;
    }
    
    // Ensure s has exactly n characters
    while |s| < n
        invariant 0 <= |s| <= n
        invariant ValidMoveSequence(s)
    {
        s := s + ['U'];
    }
}

method IntToString(n: int) returns (s: string)
    requires n >= 0
    ensures |s| > 0
    ensures forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
{
    if n == 0 {
        s := "0";
    } else {
        s := "";
        var temp := n;
        while temp > 0
            invariant temp >= 0
            invariant forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
            invariant temp > 0 || |s| > 0
        {
            var digit := temp % 10;
            s := [('0' as int + digit) as char] + s;
            temp := temp / 10;
        }
        assert |s| > 0;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures |result| > 0
    ensures result[|result| - 1] == '\n'
// </vc-spec>
// <vc-code>
{
    var n, s := ParseInput(input);
    var replacements := CountReplacements(s, 0, |s|);
    var minimized := MinimizedLength(|s|, replacements);
    result := IntToString(minimized);
    result := result + "\n";
}
// </vc-code>

