predicate ValidInput(s: string)
{
    |s| >= 1 && |s| <= 100 && forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
}

predicate ValidOutput(s: string, result: string)
{
    |result| == |s| && forall i :: 0 <= i < |result| ==> result[i] == 'x'
}

// <vc-helpers>
// If no helper proofs are needed, leave empty
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires ValidInput(s)
    ensures ValidOutput(s, result)
// </vc-spec>
// <vc-code>
{
    result := "";
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s| && |result| == i && forall j :: 0 <= j < |result| ==> result[j] == 'x'
        decreases |s| - i
    {
        result := result + "x";
        i := i + 1;
    }
}
// </vc-code>

