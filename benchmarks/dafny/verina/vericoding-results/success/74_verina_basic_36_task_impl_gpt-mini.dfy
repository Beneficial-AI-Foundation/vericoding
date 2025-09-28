// <vc-preamble>
predicate IsSpaceCommaDot(c: char)
{
    c == ' ' || c == ',' || c == '.'
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): lemma relating single-character slice to original char */
lemma CharSlicePreservesChar(s: string, i: int)
  requires 0 <= i < |s|
  ensures s[i..i+1][0] == s[i]
{
  assert |s[i..i+1]| == 1;
  assert s[i..i+1][0] == s[i];
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
  /* code modified by LLM (iteration 2): build result by concatenating single-char substrings */
  var n := |s|;
  result := "";
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == (if IsSpaceCommaDot(s[j]) then ':' else s[j])
  {
    var piece := if IsSpaceCommaDot(s[i]) then ":" else s[i..i+1];
    result := result + piece;
    i := i + 1;
  }
}

// </vc-code>
