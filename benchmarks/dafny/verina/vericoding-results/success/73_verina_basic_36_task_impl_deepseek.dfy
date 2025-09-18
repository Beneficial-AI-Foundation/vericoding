// <vc-preamble>
predicate IsSpaceCommaDot(c: char)
{
    c == ' ' || c == ',' || c == '.'
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): removed duplicate predicate */
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
  /* code modified by LLM (iteration 2): fixed string construction */
  result := "";
  if |s| > 0 {
    var chars := new char[|s|];
    var i := 0;
    while i < |s|
      invariant i <= |s|
      invariant forall j :: 0 <= j < i ==> chars[j] == (if IsSpaceCommaDot(s[j]) then ':' else s[j])
    {
      chars[i] := if IsSpaceCommaDot(s[i]) then ':' else s[i];
      i := i + 1;
    }
    result := chars[..];
  }
}
// </vc-code>
