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
/* code modified by LLM (iteration 5): The previous implementation had a logic error where `foundOtherDash` was checked after the main loop, but the 'No' result was only assigned if `S[A]` was not a '-', missing the case where `S[A]` is valid but another dash exists elsewhere. This fix ensures that if `S[A]` is not a '-', we directly return 'No'. Otherwise, we check for other dashes and return 'No' if any are found, or 'Yes' if all conditions are met, guaranteeing correct assignment to `result` and satisfying `ValidPostalCode` postconditions. */
{
  if S[A] != '-' {
    result := "No";
    return;
  }

  var foundOtherDash := false;
  var i := 0;
  while i < |S|
    invariant 0 <= i <= |S|
    invariant !foundOtherDash ==> (forall k :: 0 <= k < i && k != A ==> S[k] != '-')
  {
    if i != A && S[i] == '-' {
      foundOtherDash := true;
      break;
    }
    i := i + 1;
  }

  if foundOtherDash {
    result := "No";
  } else {
    result := "Yes";
  }
}
// </vc-code>
