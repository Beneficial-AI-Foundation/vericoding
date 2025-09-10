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
  var t := "" + c;
  assert |t| == 1;
  assert t[0] == c;
  assert |t + s| == 1 + |s|;
  // For any i in the given range, i >= |t| so (t+s)[i] == s[i - |t|]
  assert forall i :: 1 <= i < 1 + |s| ==> (t + s)[i] == s[i - |t|];
  // Since |t| == 1, replace i - |t| with i - 1
  assert forall i :: 1 <= i < 1 + |s| ==> (t + s)[i] == s[i - 1];
  assert |"" + c + s| == 1 + |s|;
}

lemma CharConcatHead(c: char, s: string)
  ensures |"" + c + s| == 1 + |s|
  ensures ("" + c + s)[0] == c
{
  var t := "" + c;
  assert |t| == 1;
  assert t[0] == c;
  assert (t + s)[0] == t[0];
  assert ("" + c + s)[0] == c;
  assert |"" + c + s| == 1 + |s|;
}

lemma Slice1_index(s: string, i: int)
  requires 1 <= i < |s|
  ensures s[1..][i - 1] == s[i]
{
  assert i - 1 + 1 == i;
  assert s[1..][i - 1] == s[i];
}

lemma ConcatPreservesRest(c: char, orig: string)
  requires |orig| > 0
  ensures forall i :: 1 <= i < |orig| ==> ("" + c + orig[1..])[i] == orig[i]
{
  // Use CharConcatIndex on orig[1..] to get the relation for indices >= 1
  CharConcatIndex(c, orig[1..]);
  // Now for each valid i, ("" + c + orig[1..])[i] == orig[1..][i-1] == orig[i]
  assert forall i :: 1 <= i < |orig| ==>
    ("" + c + orig[1..])[i] == orig[1..][i - 1];
  // Use Slice1_index to relate orig[1..][i-1] to orig[i]
  assert forall i :: 1 <= i < |orig| ==>
    orig[1..][i - 1] == orig[i];
  // Combine them
  assert forall i :: 1 <= i < |orig| ==>
    ("" + c + orig[1..])[i] == orig[i];
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

    // Length facts
    assert |output| == 1 + |input[1..]|;
    assert |input| == 1 + |input[1..]|;
    assert |output| == |input|;

    // First character is upper
    CharConcatHead(upper, input[1..]);
    assert output[0] == upper;

    // Remaining characters unchanged
    ConcatPreservesRest(upper, input);
    assert forall i :: 1 <= i < |input| ==> output[i] == input[i];

    // ToUpper preserves uppercase property
    ToUpper_props(first);
    assert output[0] == ToUpper(first);
    assert 'A' <= output[0] <= 'Z';
  } else {
    output := input;
    // From ValidInput and the branch condition, first must be uppercase
    assert ('a' <= first <= 'z') || ('A' <= first <= 'Z');
    assert !('a' <= first <= 'z');
    assert 'A' <= first <= 'Z';
    assert 'A' <= output[0] <= 'Z';

    // Remaining characters unchanged since output == input
    assert forall i :: 1 <= i < |input| ==> output[i] == input[i];
  }

  // Final length check
  assert |output| == |input|;
}
// </vc-code>

