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
function Concat(s: string, t: string): string
  ensures |Concat(s, t)| == |s| + |t|
  ensures forall i :: 0 <= i < |s| ==> Concat(s, t)[i] == s[i]
  ensures forall i :: 0 <= i < |t| ==> Concat(s, t)[|s|+i] == t[i]
{
  s + t
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

    // Proof for ValidOutput(output)
    // All characters in s and t must be 'a' through 'z' for ValidOutput to hold.
    // This is already guaranteed by ValidInput and ExtractStrings.
    // The loop in ValidInput ensures that characters before and after the space are not space or newline.
    // If they are not space or newline, and ValidInput also says overall they are 'a'..'z', then these substrings are composed of such chars.
    assert (forall i :: 0 <= i < |s| ==> ('a' <= s[i] <= 'z'));
    assert (forall i :: 0 <= i < |t| ==> ('a' <= t[i] <= 'z'));
    
    // Prove ValidOutput(output)
    assert ValidInput(input);
    assert (forall i :: 0 <= i < |s| ==> ('a' <= s[i] <= 'z')) by {
        if (|s| > 0) {
            forall i | 0 <= i < |s| ensures 'a' <= s[i] <= 'z' {
                assert 0 <= i < spacePos;
                assert input[i] != ' ' && input[i] != '\n';
                assert 'a' <= input[i] <= 'z';
                assert s[i] == input[i];
            }
        }
    }
    assert (forall i :: 0 <= i < |t| ==> ('a' <= t[i] <= 'z')) by {
        if (|t| > 0) {
            forall i | 0 <= i < |t| ensures 'a' <= t[i] <= 'z' {
                var original_index := spacePos + 1 + i;
                assert spacePos + 1 <= original_index < |input|;
                assert input[original_index] != ' ' && input[original_index] != '\n';
                assert 'a' <= input[original_index] <= 'z';
                assert t[i] == input[original_index];
            }
        }
    }

    output := Concat(t, s) + "\n";

    assert |output| == |t| + |s| + 1;
    assert |output| > 0;
    assert output[|output|-1] == '\n';
    assert (forall i :: 0 <= i < |output|-1 ==> ('a' <= output[i] <= 'z')) by {
        forall i | 0 <= i < |output|-1 ensures 'a' <= output[i] <= 'z' {
            if (i < |t|) {
                assert output[i] == t[i];
                assert 'a' <= t[i] <= 'z';
            } else {
                assert i >= |t|;
                assert i < |t| + |s|; // This is (output-1)
                assert output[i] == s[i - |t|];
                assert 'a' <= s[i - |t|] <= 'z';
            }
        }
    }
}
// </vc-code>

