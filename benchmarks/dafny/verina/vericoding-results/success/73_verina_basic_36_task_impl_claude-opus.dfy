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
  var chars := new char[|s|];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall j :: 0 <= j < i ==> chars[j] == if IsSpaceCommaDot(s[j]) then ':' else s[j]
  {
    if IsSpaceCommaDot(s[i]) {
      chars[i] := ':';
    } else {
      chars[i] := s[i];
    }
    i := i + 1;
  }
  result := chars[..];
}
// </vc-code>
