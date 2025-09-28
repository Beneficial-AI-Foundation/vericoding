// <vc-preamble>
predicate IsLowercaseLetter(c: char)
{
    'a' <= c <= 'z'
}

predicate AllLowercase(s: string)
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> IsLowercaseLetter(s[i])
}

predicate ValidOutput(result: string)
{
    result == "A" || result == "a"
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): no helpers needed */
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    ensures ValidOutput(result)
    ensures AllLowercase(input) ==> result == "a"
    ensures (|input| == 0 || !AllLowercase(input)) ==> result == "A"
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): fixed `then` keyword syntax */
{
  if AllLowercase(input) {
    result := "a";
  } else {
    result := "A";
  }
}
// </vc-code>
