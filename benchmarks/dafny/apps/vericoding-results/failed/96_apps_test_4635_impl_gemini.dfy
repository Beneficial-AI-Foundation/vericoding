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
method GeneratePattern(n: int, k: int) returns (output: string)
    requires n > 0 && k > 0 && k <= 26
    ensures CyclicPatternCorrect(n, k, output)
{
    output := "";
    var j := 0;
    while j < n
        invariant 0 <= j <= n
        invariant k > 0 && k <= 26
        invariant |output| == j
        invariant forall l :: 0 <= l < j ==> output[l] == ((l % k) + 97) as char
    {
        var char_val := j % k;
        var new_char := (char_val + 97) as char;
        output := output + new_char;
        j := j + 1;
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
    var T_str := lines[0];
    var T := StringToIntVal(T_str);

    var res: string := "";
    
    var i := 1;
    while i <= T
        invariant 1 <= i <= T + 1
        invariant T == StringToIntVal(SplitByNewline(stdin_input)[0])
        invariant |SplitByNewline(stdin_input)| >= T + 1
    {
        assert ValidInput(stdin_input);
// </vc-code>

