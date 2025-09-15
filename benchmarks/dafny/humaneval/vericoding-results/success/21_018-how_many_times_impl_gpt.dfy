// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function CountOccurrences(s: string, substr: string): int {
  |set i {:trigger} | 0 <= i <= |s| - |substr| && s[i..i+|substr|] == substr|
}
// </vc-helpers>

// <vc-spec>
method how_many_times(s: string, substr: string) returns (times: int)

    ensures times == |set i {:trigger} | 0 <= i <= |s| - |substr| && s[i..i+|substr|] == substr|
// </vc-spec>
// <vc-code>
{
  times := CountOccurrences(s, substr);
}
// </vc-code>
