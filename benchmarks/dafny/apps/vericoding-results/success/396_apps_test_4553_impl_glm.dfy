predicate ValidPostalCode(A: int, B: int, S: string)
    requires A >= 1 && B >= 1 && A <= 5 && B <= 5
    requires |S| == A + B + 1
    requires forall i :: 0 <= i < |S| ==> (S[i] == '-' || ('0' <= S[i] <= '9'))
{
    S[A] == '-' && forall i :: 0 <= i < |S| && i != A ==> S[i] != '-'
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(A: int, B: int, S: string) returns (result: string)
    requires A >= 1 && B >= 1
    requires A <= 5 && B <= 5
    requires |S| == A + B + 1
    requires forall i :: 0 <= i < |S| ==> (S[i] == '-' || ('0' <= S[i] <= '9'))
    ensures result == "Yes" || result == "No"
    ensures result == "Yes" <==> ValidPostalCode(A, B, S)
// </vc-spec>
// <vc-code>
{
    if S[A] != '-' {
        return "No";
    }
    var i := 0;
    while i < A
        invariant 0 <= i <= A
        invariant forall j :: 0 <= j < i ==> S[j] != '-'
    {
        if S[i] == '-' {
            return "No";
        }
        i := i + 1;
    }
    var j := A+1;
    while j < |S|
        invariant A+1 <= j <= |S|
        invariant forall k :: A+1 <= k < j ==> S[k] != '-'
    {
        if S[j] == '-' {
            return "No";
        }
        j := j + 1;
    }
    return "Yes";
}
// </vc-code>

