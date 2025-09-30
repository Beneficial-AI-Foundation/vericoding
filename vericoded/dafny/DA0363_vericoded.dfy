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
lemma CapitalizationPreservesLength(word: string, result: string)
  requires ValidInput(word)
  requires |result| == |word|
  requires ('A' <= result[0] <= 'Z')
  requires forall i :: 1 <= i < |word| ==> result[i] == word[i]
  requires (('a' <= word[0] <= 'z') ==> ('A' <= result[0] <= 'Z'))
  requires (('A' <= word[0] <= 'Z') ==> (result[0] == word[0]))
  ensures CorrectCapitalization(word, result)
{
}

lemma CharArithmeticLemma(c: char)
  requires 'a' <= c <= 'z'
  ensures 'A' <= (c as int - 'a' as int + 'A' as int) as char <= 'Z'
{
}

method Capitalize(word: string) returns (result: string)
  requires ValidInput(word)
  ensures CorrectCapitalization(word, result)
// </vc-helpers>

// <vc-spec>

// </vc-spec>
// <vc-code>
{
  if |word| == 0 {
    return "";
  }
  
  var firstChar := word[0];
  var capitalizedFirst: char;
  
  if 'a' <= firstChar <= 'z' {
    CharArithmeticLemma(firstChar);
    capitalizedFirst := (firstChar as int - 'a' as int + 'A' as int) as char;
  } else {
    capitalizedFirst := firstChar;
  }
  
  result := [capitalizedFirst] + word[1..];
  CapitalizationPreservesLength(word, result);
}
// </vc-code>

