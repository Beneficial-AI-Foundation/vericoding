predicate ValidInput(input: string)
{
    |input| == 3 && forall i :: 0 <= i < |input| ==> input[i] == 'A' || input[i] == 'B'
}

predicate BusServiceExists(input: string)
    requires ValidInput(input)
{
    input[0] != input[1] || input[1] != input[2]
}

// <vc-helpers>
lemma BusServiceExistsLemma(input: string)
    requires ValidInput(input)
    ensures BusServiceExists(input) <==> (input[0] != input[1] || input[1] != input[2])
{
    // The definition of BusServiceExists is directly used, no complex proof steps needed.
    // This lemma essentially just re-states the definition for clarity,
    // which can be useful in some contexts for verification,
    // but the direct definition would typically be unfolded by the verifier.
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures result == "Yes" <==> BusServiceExists(input)
    ensures result == "Yes" || result == "No"
// </vc-spec>
// <vc-code>
{
  if BusServiceExists(input)
  {
    result := "Yes";
  }
  else
  {
    result := "No";
  }
  return result;
}
// </vc-code>

