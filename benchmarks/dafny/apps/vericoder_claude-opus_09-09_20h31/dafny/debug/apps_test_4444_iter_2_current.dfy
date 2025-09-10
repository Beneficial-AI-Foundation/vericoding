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
            (forall i :: 0 <= i < |s| ==> s[i] != ' ' && s[i] != '\n' && 'a' <= s[i] <= 'z') &&
            (forall i :: 0 <= i < |t| ==> t[i] != ' ' && t[i] != '\n' && 'a' <= t[i] <= 'z')
{
    var spacePos :| 0 < spacePos < |input| && input[spacePos] == ' ' &&
                   (forall j :: 0 <= j < spacePos ==> input[j] != ' ') &&
                   (forall j :: spacePos+1 <= j < |input| ==> input[j] != ' ' && input[j] != '\n');
    
    var s := input[..spacePos];
    var t := if input[|input|-1] == '\n' then input[spacePos+1..|input|-1] else input[spacePos+1..];
    
    assert |s| == spacePos > 0;
    
    // Key insight: since spacePos < |input| and there's a valid input structure,
    // there must be at least one character after the space
    assert spacePos + 1 < |input|;  // Since spacePos < |input| and we need room for at least one char after space
    
    if input[|input|-1] == '\n' {
        assert |t| == |input| - 1 - (spacePos + 1) + 1 == |input| - spacePos - 1;
        // Since spacePos < |input| - 1 (because there's a '\n' at the end and space is not the last char)
        assert spacePos + 1 <= |input| - 1;
        assert |t| >= 1;
    } else {
        assert |t| == |input| - (spacePos + 1);
        // Since spacePos < |input| - 1 (ValidInput ensures space is not the last character)
        // We know from ValidInput that there exists such a spacePos with characters after it
        assert spacePos + 1 < |input|;  // This follows from the existence condition in ValidInput
        assert |t| >= 1;
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
    // Find the position of the space
    var spacePos := 1;
    while spacePos < |input| && input[spacePos] != ' '
        invariant 1 <= spacePos <= |input|
        invariant forall j :: 0 <= j < spacePos ==> input[j] != ' '
    {
        spacePos := spacePos + 1;
    }
    
    assert spacePos < |input| && input[spacePos] == ' ';
    assert forall j :: 0 <= j < spacePos ==> input[j] != ' ';
    
    // Extract the two strings
    var s := input[..spacePos];
    var t: string;
    
    if input[|input|-1] == '\n' {
        t := input[spacePos+1..|input|-1];
    } else {
        t := input[spacePos+1..];
    }
    
    // Verify properties needed for concatenation
    ExtractStringsProperties(input);
    assert var (s', t') := ExtractStrings(input); s == s' && t == t';
    
    // Create the output
    output := t + s + "\n";
    
    // Verify output validity
    assert |output| == |t| + |s| + 1 > 0;
    assert output[|output|-1] == '\n';
    
    // Verify all characters before newline are lowercase letters
    var i := 0;
    while i < |output| - 1
        invariant 0 <= i <= |output| - 1
        invariant forall k :: 0 <= k < i ==> 'a' <= output[k] <= 'z'
    {
        if i < |t| {
            assert output[i] == t[i];
            assert 'a' <= t[i] <= 'z';
        } else {
            assert output[i] == s[i - |t|];
            assert 'a' <= s[i - |t|] <= 'z';
        }
        i := i + 1;
    }
}
// </vc-code>

