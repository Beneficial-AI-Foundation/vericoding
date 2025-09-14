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
  /* code modified by LLM (iteration 2): Replaced for loop with while loop to avoid lower/upper bound range issues and ensure invariants prove the postconditions */
  var resultSeq: seq<char> := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |resultSeq| == i
    invariant forall j :: 0 <= j < i ==> resultSeq[j] == if IsSpaceCommaDot(s[j]) then ':' else s[j]
  {
    var newChar := if IsSpaceCommaDot(s[i]) then ':' else s[i];
    resultSeq := resultSeq + [newChar];
    i := i + 1;
  }
  result := resultSeq;
}
// </vc-code>
