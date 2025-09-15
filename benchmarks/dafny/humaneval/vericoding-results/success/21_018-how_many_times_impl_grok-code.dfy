// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added proper trigger attributes to the set comprehension to fix compilation warning */
function HowManyTimes(s: string, substr: string): int
{
  |set i {:trigger s[i..i+|substr|], i} | 0 <= i <= |s| - |substr| && s[i..i+|substr|] == substr|
}
// </vc-helpers>

// <vc-spec>
method how_many_times(s: string, substr: string) returns (times: int)

    ensures times == |set i {:trigger} | 0 <= i <= |s| - |substr| && s[i..i+|substr|] == substr|
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): assign times to the result of calling the helper function */
  times := HowManyTimes(s, substr);
}
// </vc-code>
