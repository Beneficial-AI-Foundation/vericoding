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

function toUpper(c: char): char
  requires 'a' <= c <= 'z'
  ensures 'A' <= toUpper(c) <= 'Z'
{
  ((c as int) - ('a' as int) + ('A' as int)) as char
}

predicate isLower(c: char) { 'a' <= c <= 'z' }
predicate isUpper(c: char) { 'A' <= c <= 'Z' }
predicate isLetter(c: char) { isLower(c) || isUpper(c) }

lemma ValidInputImpliesLetter(input: string)
  requires ValidInput(input)
  ensures forall i :: 0 <= i < |input| ==> isLetter(input[i])
{
}

lemma NotLowerImpliesUpper(c: char)
  requires isLetter(c)
  requires !isLower(c)
  ensures isUpper(c)
{
}
// </vc-helpers>

// <vc-spec>

// </vc-spec>
// <vc-code>
{
  var first := if ('a' <= input[0] <= 'z') then toUpper(input[0]) else input[0];
  var output := [first] + input[1..];
  output;
}
// </vc-code>

