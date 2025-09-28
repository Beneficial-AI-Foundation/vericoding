// <vc-preamble>
predicate ValidInput(input: string)
{
    |input| == 3 && forall i :: 0 <= i < |input| ==> input[i] == 'A' || input[i] == 'B'
}

predicate BusServiceExists(input: string)
    requires ValidInput(input)
{
    input[0] != input[1] || input[1] != input[2]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): The body of a lemma must be enclosed in braces. */
lemma IsDistinct(a: char, b: char, c: char) returns (distinct: bool)
{
  distinct := (a != b || b != c);
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures result == "Yes" <==> BusServiceExists(input)
    ensures result == "Yes" || result == "No"
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Added missing braces for the 'if' statement. */
{
  if (BusServiceExists(input))
  {
    result := "Yes";
  }
  else
  {
    result := "No";
  }
}
// </vc-code>
