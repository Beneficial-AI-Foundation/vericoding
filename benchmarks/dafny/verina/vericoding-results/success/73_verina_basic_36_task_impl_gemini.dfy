// <vc-preamble>
predicate IsSpaceCommaDot(c: char)
{
    c == ' ' || c == ',' || c == '.'
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ReplaceWithColon(s: string) returns (result: string)
    ensures
        |result| == |s|
    ensures
        forall i :: 0 <= i < |s| ==> 
            result[i] == 
            if IsSpaceCommaDot(s[i]) then ':' else s[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Corrected string construction syntax from char array. */
  var res_chars := new char[|s|];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall j :: 0 <= j < i ==> res_chars[j] == if IsSpaceCommaDot(s[j]) then ':' else s[j]
  {
    if IsSpaceCommaDot(s[i]) {
      res_chars[i] := ':';
    } else {
      res_chars[i] := s[i];
    }
    i := i + 1;
  }
  result := res_chars[..];
}
// </vc-code>
