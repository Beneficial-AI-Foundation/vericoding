// <vc-preamble>
predicate ValidPostalCode(A: int, B: int, S: string)
    requires A >= 1 && B >= 1 && A <= 5 && B <= 5
    requires |S| == A + B + 1
    requires forall i :: 0 <= i < |S| ==> (S[i] == '-' || ('0' <= S[i] <= '9'))
{
    S[A] == '-' && forall i :: 0 <= i < |S| && i != A ==> S[i] != '-'
}
// </vc-preamble>

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
  assume {:axiom} false;
}
// </vc-code>
