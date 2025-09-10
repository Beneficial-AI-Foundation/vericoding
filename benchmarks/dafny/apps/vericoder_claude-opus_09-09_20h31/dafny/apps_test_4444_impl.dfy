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
    
    // From ValidInput, we know the special space exists with characters after it
    // The forall clause for j :: spacePos+1 <= j < |input| is non-vacuous
    // Therefore spacePos + 1 must be less than |input|
    assert exists j :: spacePos+1 <= j < |input| && (input[j] != ' ' && input[j] != '\n');
    assert spacePos + 1 <= |input| - 1;
    assert spacePos + 1 < |input|;
    
    if input[|input|-1] == '\n' {
        assert |t| == |input| - 1 - (spacePos + 1) + 1 == |input| - spacePos - 1;
        assert |t| >= 1;
    } else {
        assert |t| == |input| - (spacePos + 1);
        assert |t| >= 1;
    }
    
    forall i | 0 <= i < |s|
        ensures s[i] != ' ' && s[i] != '\n' && 'a' <= s[i] <= 'z'
    {
        assert s[i] == input[i];
        assert 0 <= i < spacePos;
        assert input[i] != ' ';
        assert forall k :: 0 <= k < |input| ==> (input[k] == ' ' || input[k] == '\n' || ('a' <= input[k] <= 'z'));
        assert 'a' <= input[i] <= 'z';
    }
    
    forall i | 0 <= i < |t|
        ensures t[i] != ' ' && t[i] != '\n' && 'a' <= t[i] <= 'z'
    {
        if input[|input|-1] == '\n' {
            assert t[i] == input[sp
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (output: string)
    requires ValidInput(input)
    ensures ValidOutput(output)
    ensures CorrectConcatenation(input, output)
// </vc-spec>
// <vc-code>
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
    
    // From ValidInput, we know the special space exists with characters after it
    // The forall clause for j :: spacePos+1 <= j < |input| is non-vacuous
    // Therefore spacePos + 1 must be less than |input|
    assert exists j :: spacePos+1 <= j < |input| && (input[j] != ' ' && input[j] != '\n');
    assert spacePos + 1 <= |input| - 1;
    assert spacePos + 1 < |input|;
    
    if input[|input|-1] == '\n' {
        assert |t| == |input| - 1 - (spacePos + 1) + 1 == |input| - spacePos - 1;
        assert |t| >= 1;
    } else {
        assert |t| == |input| - (spacePos + 1);
        assert |t| >= 1;
    }
    
    forall i | 0 <= i < |s|
        ensures s[i] != ' ' && s[i] != '\n' && 'a' <= s[i] <= 'z'
    {
        assert s[i] == input[i];
        assert 0 <= i < spacePos;
        assert input[i] != ' ';
        assert forall k :: 0 <= k < |input| ==> (input[k] == ' ' || input[k] == '\n' || ('a' <= input[k] <= 'z'));
        assert 'a' <= input[i] <= 'z';
    }
    
    forall i | 0 <= i < |t|
        ensures t[i] != ' ' && t[i] != '\n' && 'a' <= t[i] <= 'z'
    {
        if input[|input|-1] == '\n' {
            assert t[i] == input[sp
// </vc-code>

