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
lemma Lemma_FirstCharCase(input: string, i: int)
  requires ValidInput(input)
  requires 0 <= i < |input|
  ensures (i == 0) ==> ('A' <= input[i] <= 'Z' || 'a' <= input[i] <= 'z')
{
}

lemma Lemma_CapitalizeFirstChar(input: string, output: string)
  requires ValidInput(input)
  requires |output| == |input|
  requires forall i :: 0 <= i < |output| ==> output[i] == (if i == 0 then toUpperCase(input[i]) else input[i])
  ensures CorrectCapitalization(input, output)
{
  assert 'A' <= output[0] <= 'Z';
  assert (('a' <= input[0] <= 'z') ==> ('A' <= output[0] <= 'Z'));
  assert (('A' <= input[0] <= 'Z') ==> (output[0] == input[0]));
  assert forall i :: 1 <= i < |input| ==> output[i] == input[i];
}
// </vc-helpers>

// <vc-spec>

// </vc-spec>
// <vc-code>
{
  var output := new char[|input|];
  var i := 0;
  while i < |input|
    invariant 0 <= i <= |input|
    invariant forall j :: 0 <= j < i ==> output[j] == (if j == 0 then toUpperCase(input[j]) else input[j])
  {
    if i == 0 {
      output[i] := toUpperCase(input[i]);
    } else {
      output[i] := input[i];
    }
    i := i + 1;
  }
  
  assert forall j :: 0 <= j < |output| ==> output[j] == (if j == 0 then toUpperCase(input[j]) else input[j]);
  Lemma_CapitalizeFirstChar(input, new string(output));
  return new string(output);
}
// </vc-code>

