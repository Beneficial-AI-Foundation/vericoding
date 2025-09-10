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
function ToUpper(c: char): char
{
  if 'a' <= c <= 'z' then chr(ord(c) - ord('a') + ord('A')) else c
}

lemma ToUpper_props(c: char)
  requires ('a' <= c <= 'z') || ('A' <= c <= 'Z')
  ensures 'A' <= ToUpper(c) <= 'Z'
  ensures ('A' <= c <= 'Z') ==> ToUpper(c) == c
{
  if 'a' <= c <= 'z' {
    // ord(chr(...)) simplifies to the inner integer expression when in range
    assert ord(ToUpper(c)) == ord(c) - ord('a') + ord('A');
    assert ord('A') <= ord(ToUpper(c)) <= ord('Z');
  } else {
    assert ToUpper(c) == c;
    assert 'A' <= ToUpper(c) <= 'Z';
  }
}

lemma CharConcatIndex(c: char, s: string)
  ensures |"" + c + s| == 1 + |s|
  ensures forall i :: 1 <= i < 1 + |s| ==> ("" + c + s)[i] == s[i - 1]
{
  // Prove length
  assert |""| == 0;
  // "" + c is a string of length 1 with character c at index 0
  assert |"" + c| == 1;
  assert |"" + c + s| == 1 + |s|;

  // Prove indexing property
  // For any i in 1..1+|s|-1, the i-th character of (""+c+s) is the (i-1)-th of s
  // This follows from the semantics of string concatenation.
  // We can reason by unfolding the concatenation in two steps:
  // let t := "" + c, so t[0] == c and |t| == 1, and (t + s)[i] == s[i - |t|] for i >= |t|.
  // The needed fact is direct from concat semantics; use an explicit case to help the verifier.
  var t := "" + c;
  assert |t| == 1;
  assert t[0] == c;
  // Now show the indexed equality
  // For any i with 1 <= i < 1 + |s|, we have i >= |t| and (t + s)[i] == s[i - |t|] == s[i - 1]
  assert forall i :: 1 <= i < 1 + |s| ==> (t + s)[i] == s[i - 1];
}
// </vc-helpers>

// <vc-spec>

// </vc-spec>
// <vc-code>
{
  var first := input[0];
  if 'a' <= first <= 'z' {
    var upper := ToUpper(first);
    output := "" + upper + input[1..];

    // length and index facts for concatenation
    CharConcatIndex(upper, input[1..]);
    assert |output| == 1 + |input[1..]|;
    assert |input[1..]| == |input| - 1;
  } else {
    output := input;
  }

  // Final postcondition checks
  assert |output| == |input|;

  // First character is uppercase
  if 'a' <= first <= 'z' {
    ToUpper_props(first);
    assert output[0] == ToUpper(first);
    assert 'A' <= output[0] <= 'Z';
  } else {
    // first is already uppercase by the branch condition
    assert 'A' <= output[0] <= 'Z';
  }

  // All remaining characters unchanged
  assert forall i :: 1 <= i < |input| ==> output[i] == input[i];
}
// </vc-code>

