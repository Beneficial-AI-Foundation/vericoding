predicate ValidInput(input: string)
{
    |input| > 0 && 
    (exists lines :: lines == SplitByNewline(input) && 
     |lines| >= 1 && 
     IsValidInteger(lines[0]) &&
     StringToIntVal(lines[0]) >= 0 &&
     |lines| >= StringToIntVal(lines[0]) + 1 &&
     (forall i :: 1 <= i <= StringToIntVal(lines[0]) && i < |lines| ==> ValidTestCaseLine(lines[i])))
}

predicate ValidTestCaseLine(line: string)
{
    exists parts :: (parts == SplitBySpace(line) &&
                    |parts| >= 2 &&
                    IsValidInteger(parts[0]) &&
                    IsValidInteger(parts[1]) &&
                    StringToIntVal(parts[0]) > 0 &&
                    StringToIntVal(parts[1]) > 0 &&
                    StringToIntVal(parts[1]) <= 26)
}

predicate IsValidInteger(s: string)
{
    |s| > 0 && 
    (|s| == 1 || s[0] != '0' || s == "0") &&
    forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

function StringToIntVal(s: string): int
    requires IsValidInteger(s)
    ensures StringToIntVal(s) >= 0
{
    if |s| == 0 then 0 else
    if |s| == 1 then (s[0] as int) - 48 else
    StringToIntVal(s[0..|s|-1]) * 10 + ((s[|s|-1] as int) - 48)
}

predicate CyclicPatternCorrect(n: int, k: int, output: string)
    requires n > 0 && k > 0 && k <= 26
{
    |output| == n &&
    (forall j :: 0 <= j < n ==> output[j] == ((j % k) + 97) as char)
}

// <vc-helpers>
function SplitByNewline(s: string): seq<string>
{
    if |s| == 0 then []
    else if |s| == 1 then [s]
    else if s[0] == '\n' then [""] + SplitByNewline(s[1..])
    else 
        var rest := SplitByNewline(s[1..]);
        if |rest| == 0 then [s]
        else [s[0..1] + rest[0]] + rest[1..]
}

function SplitBySpace(s: string): seq<string>
{
    if |s| == 0 then []
    else if |s| == 1 then [s]
    else if s[0] == ' ' then [""] + SplitBySpace(s[1..])
    else 
        var rest := SplitBySpace(s[1..]);
        if |rest| == 0 then [s]
        else [s[0..1] + rest[0]] + rest[1..]
}

function GenerateCyclicPattern(n: int, k: int): string
    requires n > 0 && k > 0 && k <= 26
    ensures |GenerateCyclicPattern(n, k)| == n
    ensures CyclicPatternCorrect(n, k, GenerateCyclicPattern(n, k))
{
    seq(n, i requires 0 <= i < n => ((i % k) + 97) as char)
}

lemma GenerateCyclicPatternCorrect(n: int, k: int)
    requires n > 0 && k > 0 && k <= 26
    ensures CyclicPatternCorrect(n, k, GenerateCyclicPattern(n, k))
{
    var pattern := GenerateCyclicPattern(n, k);
    assert |pattern| == n;
    forall j | 0 <= j < n
        ensures pattern[j] == ((j % k) + 97) as char
    {
        assert pattern[j] == ((j % k) + 97) as char;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires ValidInput(stdin_input)
    ensures |result| >= 0
// </vc-spec>
// <vc-code>
{
    var lines := SplitByNewline(stdin_input);
    var t := StringToIntVal(lines[0]);
    var outputs: seq<string> := [];
    
    var i := 0;
    while i < t
        invariant 0 <= i <= t
        invariant |outputs| == i
    {
        var testCaseLine := lines[i + 1];
        var parts := SplitBySpace(testCaseLine);
        var n := StringToIntVal(parts[0]);
        var k := StringToIntVal(parts[1]);
        
        GenerateCyclicPatternCorrect(n, k);
        var pattern := GenerateCyclicPattern(n, k);
        outputs := outputs + [pattern];
        
        i := i + 1;
    }
    
    if |outputs| == 0 {
        result := "";
    } else {
        result := outputs[0];
        var j := 1;
        while j < |outputs|
            invariant 1 <= j <= |outputs|
        {
            result := result + "\n" + outputs[j];
            j := j + 1;
        }
    }
}
// </vc-code>

