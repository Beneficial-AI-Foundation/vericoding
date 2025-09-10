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
lemma Lem_CommasToSpaces_Length(s: string)
  requires ValidInput(s)
  ensures |CommasToSpaces(s)| == |s|
{
}

lemma Lem_CommasToSpaces_Characters(s: string)
  requires ValidInput(s)
  ensures forall i :: 0 <= i < |s| ==> 
    (s[i] == ',' ==> CommasToSpaces(s)[i] == ' ') &&
    (s[i] != ',' ==> CommasToSpaces(s)[i] == s[i])
{
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
  requires ValidInput(s)
  ensures CorrectOutput(s, result)
// </vc-spec>
// <vc-code>
{
  var sb: string := "";
  var i: nat := 0;
  
  while i < |s| 
    invariant i <= |s|
    invariant |sb| == i
    invariant forall j :: 0 <= j < i ==> 
      (s[j] == ',' ==> sb[j] == ' ') && 
      (s[j] != ',' ==> sb[j] == s[j])
  {
    if s[i] == ',' {
      sb := sb + [' '];
    } else {
      sb := sb + [s[i]];
    }
    i := i + 1;
  }
  
  result := sb + ['\n'];
}
// </vc-code>

