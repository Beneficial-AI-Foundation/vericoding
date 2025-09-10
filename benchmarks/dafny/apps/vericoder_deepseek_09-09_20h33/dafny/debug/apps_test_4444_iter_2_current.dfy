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
        (forall i :: 0 <= i < |s| ==> s[i] != ' ' && s[i] != '\n') &&
        (forall i :: 0 <= i < |t| ==> t[i] != ' ' && t[i] != '\n') &&
        input == s + " " + t + (if input[|input|-1] == '\n' then "\n" else "")
{
    var spacePos :| 0 < spacePos < |input| && input[spacePos] == ' ' &&
                   (forall j :: 0 <= j < spacePos ==> input[j] != ' ') &&
                   (forall j :: spacePos+1 <= j < |input| ==> input[j] != ' ' && input[j] != '\n');
    var s := input[..spacePos];
    var t := if input[|input|-1] == '\n' then input[spacePos+1..|input|-1] else input[spacePos+1..];
    
    assert |s| > 0 by {
        assert input[0] != ' ' && input[0] != '\n';
    }
    assert |t| > 0 by {
        assert input[|input|-1] != ' ' && input[|input|-1] != '\n' || 
               (input[|input|-1] == '\n' && input[|input|-2] != ' ' && input[|input|-2] != '\n');
    }
}

lemma StringConcatenationProperties(s: string, t: string)
    requires |s| > 0 && |t| > 0
    requires forall i :: 0 <= i < |s| ==> s[i] != ' ' && s[i] != '\n' && ('a' <= s[i] <= 'z')
    requires forall i :: 0 <= i < |t| ==> t[i] != ' ' && t[i] != '\n' && ('a' <= t[i] <= 'z')
    ensures |t + s + "\n"| > 0
    ensures (t + s + "\n")[|t + s + "\n"|-1] == '\n'
    ensures forall i :: 0 <= i < |t + s + "\n"|-1 ==> ('a' <= (t + s + "\n")[i] <= 'z')
{
    assert |t + s + "\n"| == |t| + |s| + 1;
    assert (t + s + "\n")[|t| + |s|] == '\n';
    
    forall i | 0 <= i < |t| + |s|
        ensures ('a' <= (t + s + "\n")[i] <= 'z')
    {
        if i < |t| {
            assert (t + s + "\n")[i] == t[i];
        } else {
            assert (t + s + "\n")[i] == s[i - |t|];
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
    var spacePos :| 0 < spacePos < |input| && input[spacePos] == ' ' &&
                   (forall j :: 0 <= j < spacePos ==> input[j] != ' ') &&
                   (forall j :: spacePos+1 <= j < |input| ==> input[j] != ' ' && input[j] != '\n');
    
    var s := input[..spacePos];
    var t := if input[|input|-1] == '\n' then input[spacePos+1..|input|-1] else input[spacePos+1..];
    
    ExtractStringsProperties(input);
    StringConcatenationProperties(s, t);
    
    output := t + s + "\n";
}
// </vc-code>

