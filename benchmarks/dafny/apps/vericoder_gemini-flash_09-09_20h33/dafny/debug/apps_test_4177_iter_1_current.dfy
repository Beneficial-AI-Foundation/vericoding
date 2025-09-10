predicate ValidInput(s: string)
{
    |s| >= 1 && |s| <= 100 && forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
}

predicate ValidOutput(s: string, result: string)
{
    |result| == |s| && forall i :: 0 <= i < |result| ==> result[i] == 'x'
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires ValidInput(s)
    ensures ValidOutput(s, result)
// </vc-spec>
// <vc-code>
{
    var new_s := new char[|s|];
    for i := 0 to |s| - 1
        decreases |s| - i
        ensures i < |s| ==> forall k :: 0 <= k <= i ==> new_s[k] == 'x'
    {
        new_s[i] := 'x';
    }
    return new_s as string;
}
// </vc-code>

