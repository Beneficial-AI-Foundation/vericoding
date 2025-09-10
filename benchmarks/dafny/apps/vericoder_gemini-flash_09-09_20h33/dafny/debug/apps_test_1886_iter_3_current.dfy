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
function CharToUpper(c: char): char
  requires 'a' <= c <= 'z'
  ensures 'A' <= CharToUpper(c) <= 'Z'
{
  (c as int - 'a' as int + 'A' as int) as char
}
// </vc-helpers>

// <vc-spec>

// </vc-spec>
// <vc-code>
{
    var output_chars := new char[|input|];
    if 'a' <= input[0] <= 'z' {
        output_chars[0] := CharToUpper(input[0]);
    } else {
        output_chars[0] := input[0];
    }
    for i := 1 to |input| - 1
      invariant 1 <= i <= |input|
      invariant forall k :: 0 <= k < i ==> output_chars[k] == input[k] || (k == 0 && 'A' <= output_chars[0] <= 'Z')
    {
        output_chars[i] := input[i];
    }
    return output_chars;
}
// </vc-code>

