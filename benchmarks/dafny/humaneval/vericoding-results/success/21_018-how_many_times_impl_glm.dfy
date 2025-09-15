// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added explicit trigger for quantifier */
function OccurrenceIndices(s: string, substr: string): set<int> { set i {:trigger s[i..i+|substr|]} | 0 <= i <= |s| - |substr| && s[i..i+|substr|] == substr }
// </vc-helpers>

// <vc-spec>
method how_many_times(s: string, substr: string) returns (times: int)

    ensures times == |set i {:trigger} | 0 <= i <= |s| - |substr| && s[i..i+|substr|] == substr|
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): using OccurrenceIndices helper function */
  times := |OccurrenceIndices(s, substr)|;
}
// </vc-code>
