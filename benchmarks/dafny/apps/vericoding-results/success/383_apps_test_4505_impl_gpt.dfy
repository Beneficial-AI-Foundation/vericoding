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
// (no changes needed)
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

  // Prove |input_chars| == 3
  if |s| == 3 {
    assert input_chars == s;
    assert |input_chars| == 3;
  } else {
    assert |s| == 4;
    assert input_chars == s[..3];
    assert |input_chars| == 3;
  }

  // Prove membership of characters in {'a','b','c'} for input_chars
  forall i | 0 <= i < |input_chars|
    ensures input_chars[i] == 'a' || input_chars[i] == 'b' || input_chars[i] == 'c'
  {
    if |s| == 3 {
      assert input_chars == s;
      assert |input_chars| == |s|;
      assert 0 <= i < |s|;
      assert 0 <= i < (if |s| == 4 then 3 else |s|);
      assert s[i] == 'a' || s[i] == 'b' || s[i] == 'c';
      assert input_chars[i] == s[i];
    } else {
      assert |s| == 4;
      assert input_chars == s[..3];
      assert |input_chars| == 3;
      assert 0 <= i < 3;
      assert 0 <= i < (if |s| == 4 then 3 else |s|);
      assert s[i] == 'a' || s[i] == 'b' || s[i] == 'c';
      assert input_chars[i] == s[i];
    }
  }

  // Decide result based on pairwise distinctness
  var yes := input_chars[0] != input_chars[1] &&
             input_chars[1] != input_chars[2] &&
             input_chars[0] != input_chars[2];

  // Relate yes to the specification predicate
  assert IsPermutationOfABC(input_chars) <==> yes;

  if yes {
    result := "Yes\n";
  } else {
    result := "No\n";
  }
}
// </vc-code>

