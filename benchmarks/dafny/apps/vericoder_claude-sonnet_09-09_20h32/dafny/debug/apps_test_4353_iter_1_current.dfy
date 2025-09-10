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
lemma CommasToSpacesCorrect(s: string)
  requires ValidInput(s)
  ensures var converted := CommasToSpaces(s);
          |converted| == |s| &&
          forall i :: 0 <= i < |s| ==> 
            (s[i] == ',' ==> converted[i] == ' ') &&
            (s[i] != ',' ==> converted[i] == s[i])
{
  var converted := CommasToSpaces(s);
  assert |converted| == |s|;
  forall i | 0 <= i < |s|
    ensures (s[i] == ',' ==> converted[i] == ' ') &&
            (s[i] != ',' ==> converted[i] == s[i])
  {
    assert converted[i] == (if s[i] == ',' then ' ' else s[i]);
  }
}

lemma ConcatenationLength(s: string)
  requires ValidInput(s)
  ensures |s + "\n"| == |s| + 1
{
}

lemma ConcatenationProperties(s: string)
  requires ValidInput(s)
  ensures var result := CommasToSpaces(s) + "\n";
          |result| == |s| + 1 &&
          result[|result| - 1] == '\n' &&
          forall i :: 0 <= i < |s| ==> result[i] == CommasToSpaces(s)[i]
{
  var converted := CommasToSpaces(s);
  var result := converted + "\n";
  assert |result| == |converted| + |"\n"|;
  assert |"\n"| == 1;
  assert |result| == |converted| + 1;
  assert |converted| == |s|;
  assert result[|result| - 1] == '\n';
  
  forall i | 0 <= i < |s|
    ensures result[i] == converted[i]
  {
    assert i < |converted|;
    assert result[i] == converted[i];
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
  var converted := CommasToSpaces(s);
  result := converted + "\n";
  
  CommasToSpacesCorrect(s);
  ConcatenationProperties(s);
}
// </vc-code>

