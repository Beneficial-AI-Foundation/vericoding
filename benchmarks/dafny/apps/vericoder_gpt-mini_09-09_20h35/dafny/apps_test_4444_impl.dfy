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
lemma ExtractStringsChars(input: string)
    requires ValidInput(input)
    ensures forall i :: 0 <= i < |ExtractStrings(input).0| ==> 'a' <= ExtractStrings(input).0[i] <= 'z'
    ensures forall i :: 0 <= i < |ExtractStrings(input).1| ==> 'a' <= ExtractStrings(input).1[i] <= 'z'
{
  var (s,t) := ExtractStrings(input);

  // s is the prefix up to the space position
  assert 0 < |s| < |input|;
  assert input[|s|] == ' ';
  assert s == input[..|s|];
  // From the way ExtractStrings picks the space position, characters before it are not space/newline
  assert forall j :: 0 <= j < |s| ==> input[j] != ' ' && input[j] != '\n';
  // Characters of s are same as corresponding input characters
  assert forall i :: 0 <= i < |s| ==> s[i] == input[i];
  // Using ValidInput's character restriction, these must be lowercase letters
  assert forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z';

  // t is the suffix after the space position (excluding a trailing newline if present)
  if input[|input|-1] == '\n' {
    assert t == input[|s|+1..|input|-1];
    assert forall j :: |s|+1 <= j < |input| ==> input[j] != ' ' && input[j] != '\n';
    assert forall k :: 0 <= k < |t| ==> t[k] == input[|s|+1 + k];
    assert forall k :: 0 <= k < |t| ==> 'a' <= t[k] <= 'z';
  } else {
    assert t == input[|s|+1..];
    assert forall j :: |s|+1 <= j < |input| ==> input[j] != ' ' && input[j] != '\n';
    assert forall k :: 0 <= k < |t| ==> t[k] == input[|s|+1 + k];
    assert forall k :: 0 <= k < |t| ==> 'a' <= t[k] <= 'z';
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
  ExtractStringsChars(input);
  output := t + s + "\n";
  assert |output| > 0;
  assert output[|output|-1] == '\n';
  assert forall i :: 0 <= i < |output|-1 ==> 'a' <= output[i] <= 'z';
}
// </vc-code>

