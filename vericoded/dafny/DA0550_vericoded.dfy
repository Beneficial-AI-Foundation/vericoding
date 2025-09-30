predicate ValidInput(s: string)
{
  |s| == 19 && 
  |s| >= 2 && s[5] == ',' && s[13] == ',' &&
  forall i :: 0 <= i < |s| ==> (s[i] == ',' || ('a' <= s[i] <= 'z'))
}

function CommasToSpaces(s: string): string
  requires ValidInput(s)
{
  seq(|s|, i requires 0 <= i < |s| => if s[i] == ',' then ' ' else s[i])
}

predicate CorrectOutput(s: string, result: string)
  requires ValidInput(s)
{
  |result| == |s| + 1 &&
  result[|result| - 1] == '\n' &&
  forall i :: 0 <= i < |s| ==> 
    (s[i] == ',' ==> result[i] == ' ') &&
    (s[i] != ',' ==> result[i] == s[i])
}

// <vc-helpers>
lemma CommasToSpacesCorrectness(s: string)
  requires ValidInput(s)
  ensures |CommasToSpaces(s)| == |s|
  ensures forall i :: 0 <= i < |s| ==> 
    (s[i] == ',' ==> CommasToSpaces(s)[i] == ' ') &&
    (s[i] != ',' ==> CommasToSpaces(s)[i] == s[i])
{
  var transformed := CommasToSpaces(s);
  assert |transformed| == |s|;
  forall i | 0 <= i < |s|
    ensures s[i] == ',' ==> transformed[i] == ' '
    ensures s[i] != ',' ==> transformed[i] == s[i]
  {
    assert transformed[i] == if s[i] == ',' then ' ' else s[i];
  }
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
  requires ValidInput(s)
  ensures CorrectOutput(s, result)
// </vc-spec>
// <vc-code>
{
  var transformed := CommasToSpaces(s);
  result := transformed + "\n";
  
  CommasToSpacesCorrectness(s);
  
  assert |result| == |transformed| + 1 == |s| + 1;
  assert result[|result| - 1] == '\n';
  
  forall i | 0 <= i < |s|
    ensures s[i] == ',' ==> result[i] == ' '
    ensures s[i] != ',' ==> result[i] == s[i]
  {
    assert result[i] == transformed[i];
    assert s[i] == ',' ==> transformed[i] == ' ';
    assert s[i] != ',' ==> transformed[i] == s[i];
  }
}
// </vc-code>

