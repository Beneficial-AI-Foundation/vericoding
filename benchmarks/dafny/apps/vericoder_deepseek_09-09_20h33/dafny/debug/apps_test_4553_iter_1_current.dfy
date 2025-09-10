predicate ValidPostalCode(A: int, B: int, S: string)
    requires A >= 1 && B >= 1 && A <= 5 && B <= 5
    requires |S| == A + B + 1
    requires forall i :: 0 <= i < |S| ==> (S[i] == '-' || ('0' <= S[i] <= '9'))
{
    S[A] == '-' && forall i :: 0 <= i < |S| && i != A ==> S[i] != '-'
}

// <vc-helpers>
lemma PostalCodeLemma(A: int, B: int, S: string)
    requires A >= 1 && B >= 1 && A <= 5 && B <= 5
    requires |S| == A + B + 1
    requires forall i :: 0 <= i < |S| ==> (S[i] == '-' || ('0' <= S[i] <= '9'))
    ensures ValidPostalCode(A, B, S) <==> (S[A] == '-' && forall i :: 0 <= i < |S| && i != A ==> S[i] != '-')
{
}
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
    var dashPos := A;
    if S[dashPos] != '-' {
        result := "No";
        return;
    }
    
    var i := 0;
    while i < |S|
        invariant 0 <= i <= |S|
        invariant forall j :: 0 <= j < i && j != dashPos ==> S[j] != '-'
    {
        if i != dashPos && S[i] == '-' {
            result := "No";
            return;
        }
        i := i + 1;
    }
    
    result := "Yes";
}
// </vc-code>

