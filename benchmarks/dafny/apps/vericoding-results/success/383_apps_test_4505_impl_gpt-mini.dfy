predicate ValidInput(s: string)
{
    (|s| == 3 || (|s| == 4 && s[3] == '\n')) &&
    forall i :: 0 <= i < (if |s| == 4 then 3 else |s|) ==> (s[i] == 'a' || s[i] == 'b' || s[i] == 'c')
}

function GetInputChars(s: string): string
    requires ValidInput(s)
{
    if |s| == 4 then s[..3] else s
}

predicate IsPermutationOfABC(input_chars: string)
    requires |input_chars| == 3
    requires forall i :: 0 <= i < |input_chars| ==> (input_chars[i] == 'a' || input_chars[i] == 'b' || input_chars[i] == 'c')
{
    input_chars[0] != input_chars[1] && 
    input_chars[1] != input_chars[2] && 
    input_chars[0] != input_chars[2]
}

// <vc-helpers>
lemma GetInputCharsProps(s: string)
    requires ValidInput(s)
    ensures |GetInputChars(s)| == 3
    ensures forall i :: 0 <= i < 3 ==> (GetInputChars(s)[i] == 'a' || GetInputChars(s)[i] == 'b' || GetInputChars(s)[i] == 'c')
{
  if |s| == 4 {
    // GetInputChars(s) == s[..3]
    assert GetInputChars(s) == s[..3];
    assert |GetInputChars(s)| == 3;
    var i := 0;
    while i < 3
      invariant 0 <= i <= 3
    {
      assert 0 <= i < |s|;
      assert GetInputChars(s)[i] == s[i];
      assert s[i] == 'a' || s[i] == 'b' || s[i] == 'c';
      i := i + 1;
    }
  } else {
    // GetInputChars(s) == s
    assert GetInputChars(s) == s;
    assert |GetInputChars(s)| == 3;
    var i := 0;
    while i < 3
      invariant 0 <= i <= 3
    {
      assert GetInputChars(s)[i] == s[i];
      assert s[i] == 'a' || s[i] == 'b' || s[i] == 'c';
      i := i + 1;
    }
  }
}

lemma Unfold_IsPermutationOfABC(input_chars: string)
    requires |input_chars| == 3
    requires forall i :: 0 <= i < 3 ==> (input_chars[i] == 'a' || input_chars[i] == 'b' || input_chars[i] == 'c')
    ensures IsPermutationOfABC(input_chars) == (input_chars[0] != input_chars[1] && input_chars[1] != input_chars[2] && input_chars[0] != input_chars[2])
{
  // The predicate IsPermutationOfABC is defined exactly as the right-hand side,
  // so we can assert their equality.
  assert IsPermutationOfABC(input_chars) == (input_chars[0] != input_chars[1] && input_chars[1] != input_chars[2] && input_chars[0] != input_chars[2]);
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires |s| >= 3
    requires ValidInput(s)
    ensures result == "Yes\n" || result == "No\n"
    ensures result == "Yes\n" <==> IsPermutationOfABC(GetInputChars(s))
// </vc-spec>
// <vc-code>
{
  var input_chars := GetInputChars(s);
  GetInputCharsProps(s);
  Unfold_IsPermutationOfABC(input_chars);
  var b := input_chars[0] != input_chars[1] && input_chars[1] != input_chars[2] && input_chars[0] != input_chars[2];
  if b {
    result := "Yes\n";
  } else {
    result := "No\n";
  }
  // Relate result to the boolean b and to the predicate
  assert (result == "Yes\n") <==> b;
  assert b == (input_chars[0] != input_chars[1] && input_chars[1] != input_chars[2] && input_chars[0] != input_chars[2]);
  assert (IsPermutationOfABC(input_chars) == (input_chars[0] != input_chars[1] && input_chars[1] != input_chars[2] && input_chars[0] != input_chars[2]));
  assert (result == "Yes\n") <==> IsPermutationOfABC(input_chars);
}
// </vc-code>

