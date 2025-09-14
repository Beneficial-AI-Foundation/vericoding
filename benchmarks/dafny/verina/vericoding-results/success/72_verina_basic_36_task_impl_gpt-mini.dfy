// <vc-preamble>
predicate IsSpaceCommaDot(c: char)
{
    c == ' ' || c == ',' || c == '.'
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): convert space/comma/dot to colon */
function Convert(c: char): char { if IsSpaceCommaDot(c) then ':' else c }
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
  /* code modified by LLM (iteration 2): build result by concatenating substrings */
  var n := |s|;
  result := "";
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == Convert(s[j])
  {
    if IsSpaceCommaDot(s[i]) {
      result := result + ":";
    } else {
      result := result + s[i..i+1];
    }
    i := i + 1;
  }
  assert |result| == n;
  assert forall k :: 0 <= k < n ==> result[k] == Convert(s[k]);
}
// </vc-code>
