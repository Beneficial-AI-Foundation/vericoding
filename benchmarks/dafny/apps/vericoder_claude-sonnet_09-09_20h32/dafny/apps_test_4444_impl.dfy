predicate ValidInput(input: string)
{
    |input| > 2 &&
    (exists i :: 0 < i < |input| && input[i] == ' ') &&
    (forall i :: 0 <= i < |input| ==> (input[i] == ' ' || input[i] == '\n' || ('a' <= input[i] <= 'z'))) &&
    (exists i :: 0 < i < |input| && input[i] == ' ' && 
     (forall j :: 0 <= j < i ==> input[j] != ' ' && input[j] != '\n') &&
     (forall j :: i+1 <= j < |input| ==> input[j] != ' ' && input[j] != '\n'))
}

predicate ValidOutput(output: string)
{
    |output| > 0 &&
    output[|output|-1] == '\n' &&
    (forall i :: 0 <= i < |output|-1 ==> ('a' <= output[i] <= 'z'))
}

function ExtractStrings(input: string): (string, string)
    requires ValidInput(input)
{
    var spacePos :| 0 < spacePos < |input| && input[spacePos] == ' ' &&
                   (forall j :: 0 <= j < spacePos ==> input[j] != ' ') &&
                   (forall j :: spacePos+1 <= j < |input| ==> input[j] != ' ' && input[j] != '\n');
    var s := input[..spacePos];
    var t := if input[|input|-1] == '\n' then input[spacePos+1..|input|-1] else input[spacePos+1..];
    (s, t)
}

predicate CorrectConcatenation(input: string, output: string)
    requires ValidInput(input)
{
    var (s, t) := ExtractStrings(input);
    output == t + s + "\n"
}

// <vc-helpers>
lemma ExtractStringsProperties(input: string)
    requires ValidInput(input)
    ensures var (s, t) := ExtractStrings(input);
            |s| > 0 && |t| > 0 &&
            (forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z') &&
            (forall i :: 0 <= i < |t| ==> 'a' <= t[i] <= 'z')
{
    var (s, t) := ExtractStrings(input);
    var spacePos :| 0 < spacePos < |input| && input[spacePos] == ' ' &&
                   (forall j :: 0 <= j < spacePos ==> input[j] != ' ') &&
                   (forall j :: spacePos+1 <= j < |input| ==> input[j] != ' ' && input[j] != '\n');
    
    assert s == input[..spacePos];
    assert |s| == spacePos > 0;
    
    // From ValidInput, we know there exists such a space position
    // The constraint (forall j :: spacePos+1 <= j < |input| ==> input[j] != ' ' && input[j] != '\n')
    // combined with spacePos < |input| means there must be at least one character after space
    // that is not a space or newline, which means spacePos+1 < |input|
    assert spacePos+1 < |input|;
    
    if input[|input|-1] == '\n' {
        // If last char is newline, t excludes it
        assert t == input[spacePos+1..|input|-1];
        assert |t| == |input| - 1 - (spacePos + 1);
        assert |t| == |input| - spacePos - 2;
        // Since spacePos+1 < |input|, we have |input| - spacePos - 2 >= 0
        // But we need |t| > 0, which means |input| - spacePos - 2 > 0
        // This gives us spacePos < |input| - 2
        assert spacePos < |input| - 2;
        assert |t| > 0;
    } else {
        assert t == input[spacePos+1..];
        assert |t| == |input| - spacePos - 1;
        assert |t| > 0;
    }
}

lemma ConcatenationValidOutput(input: string)
    requires ValidInput(input)
    ensures var (s, t) := ExtractStrings(input);
            ValidOutput(t + s + "\n")
{
    var (s, t) := ExtractStrings(input);
    ExtractStringsProperties(input);
    var result := t + s + "\n";
    
    assert |result| == |t| + |s| + 1 > 0;
    assert result[|result|-1] == '\n';
    
    forall i | 0 <= i < |result|-1
        ensures 'a' <= result[i] <= 'z'
    {
        if i < |t| {
            assert result[i] == t[i];
        } else {
            assert result[i] == s[i - |t|];
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (output: string)
    requires ValidInput(input)
    ensures ValidOutput(output)
    ensures CorrectConcatenation(input, output)
// </vc-spec>
// <vc-code>
{
    var (s, t) := ExtractStrings(input);
    ExtractStringsProperties(input);
    output := t + s + "\n";
    ConcatenationValidOutput(input);
}
// </vc-code>

