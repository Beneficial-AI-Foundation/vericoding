// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate MatchAt(s: string, t: string, i: int)
{
  0 <= i <= |s| - |t| && s[i..i+|t|] == t
}

/* helper modified by LLM (iteration 2): added explicit trigger to set comprehension in OccurrenceCount to improve quantifier instantiation */
function OccurrenceCount(s: string, t: string): int
{
  |set i {:trigger} | 0 <= i <= |s| - |t| && s[i..i+|t|] == t|
}
// </vc-helpers>

// <vc-spec>
method how_many_times(s: string, substr: string) returns (times: int)

    ensures times == |set i {:trigger} | 0 <= i <= |s| - |substr| && s[i..i+|substr|] == substr|
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): compute count directly using helper function to satisfy postcondition */
  times := OccurrenceCount(s, substr);
}
// </vc-code>
