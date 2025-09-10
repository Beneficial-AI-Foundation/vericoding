predicate ValidInput(word: string)
{
  |word| > 0 && forall i :: 0 <= i < |word| ==> ('a' <= word[i] <= 'z') || ('A' <= word[i] <= 'Z')
}

predicate CorrectCapitalization(input: string, output: string)
  requires ValidInput(input)
{
  |output| == |input| &&
  ('A' <= output[0] <= 'Z') &&
  (('a' <= input[0] <= 'z') ==> ('A' <= output[0] <= 'Z')) &&
  (('A' <= input[0] <= 'Z') ==> (output[0] == input[0])) &&
  forall i :: 1 <= i < |input| ==> output[i] == input[i]
}

// <vc-helpers>
// No additional helpers required for this implementation.
// </vc-helpers>

// <vc-spec>

// </vc-spec>
// <vc-code>
{
  var first := input[0];
  if 'a' <= first <= 'z' {
    var upper := char((first - 'a') + 'A');
    output := "" + upper + input[1..];
  } else {
    output := input;
  }

  assert |output| == |input|;
  assert 'A' <= output[0] <= 'Z';
  assert forall i :: 1 <= i < |input| ==> output[i] == input[i];
}
// </vc-code>

