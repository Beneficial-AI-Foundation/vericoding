// <vc-preamble>
predicate IsSpaceCommaDot(c: char)
{
    c == ' ' || c == ',' || c == '.'
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added recursive builder for the result string */
function BuildSeq(s: string, n: nat): string
  requires n <= |s|
  ensures |BuildSeq(s, n)| == n
  ensures forall i :: 0 <= i < n ==> BuildSeq(s, n)[i] == if IsSpaceCommaDot(s[i]) then ':' else s[i]
{
  if n == 0 then "" else BuildSeq(s, n-1) + [if IsSpaceCommaDot(s[n-1]) then ':' else s[n-1]]
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
  /* code modified by LLM (iteration 3): use recursive helper to construct result */
  result := BuildSeq(s, |s|);
}
// </vc-code>
