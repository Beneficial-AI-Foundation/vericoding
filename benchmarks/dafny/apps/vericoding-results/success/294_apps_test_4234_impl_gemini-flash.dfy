// <vc-preamble>
predicate ValidInput(n: int, s: string)
{
    n == |s| && n >= 0
}

predicate IsGoodString(s: string)
{
    |s| % 2 == 0 && forall i :: 0 <= i < |s|/2 ==> s[2*i] != s[2*i+1]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): No changes needed for helper function. */
function IsGoodStringLen(s: string): (len: int)
{
    if |s| == 0 then 0
    else if |s| % 2 == 0 && forall i :: 0 <= i < |s|/2 ==> s[2*i] != s[2*i+1] then |s|
    else 0
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, s: string) returns (deletedCount: int, result: string)
    requires ValidInput(n, s)
    ensures deletedCount >= 0
    ensures deletedCount == |s| - |result|
    ensures IsGoodString(result)
    ensures deletedCount + |result| == |s|
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Fixed compilation error where `new string(res[..writeIdx])` was incorrect; changed to `res[..writeIdx]`. Also, adjusted loop invariant to correctly reflect `IsGoodString` for characters written to `res`. */
{
    var res := new char[|s|];
    var writeIdx := 0;
    deletedCount := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant 0 <= writeIdx <= i
        invariant deletedCount == i - writeIdx
        invariant writeIdx % 2 == 0
        invariant forall k :: 0 <= k < writeIdx / 2 ==> res[2 * k] != res[2 * k + 1]
    {
        if i + 1 < |s| && s[i] != s[i+1]
        {
            res[writeIdx] := s[i];
            res[writeIdx+1] := s[i+1];
            writeIdx := writeIdx + 2;
            i := i + 2;
        }
        else
        {
            deletedCount := deletedCount + 1;
            i := i + 1;
        }
    }
    result := res[..writeIdx];
}
// </vc-code>
