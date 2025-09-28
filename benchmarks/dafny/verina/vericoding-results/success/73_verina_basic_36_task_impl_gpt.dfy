// <vc-preamble>
predicate IsSpaceCommaDot(c: char)
{
    c == ' ' || c == ',' || c == '.'
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): switched to pure function (no 'method'); returns ':' for space/comma/dot */
function ReplaceCharIfSpaceCommaDot(c: char): char
{
  if IsSpaceCommaDot(c) then ':' else c
}
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
  /* code modified by LLM (iteration 2): iterate through string and replace spaces/commas/dots with ':' using helper */
  var i := 0;
  result := "";
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == (if IsSpaceCommaDot(s[j]) then ':' else s[j])
    decreases |s| - i
  {
    var ch := ReplaceCharIfSpaceCommaDot(s[i]);
    result := result + [ch];
    i := i + 1;
  }
}
// </vc-code>
