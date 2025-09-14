predicate ValidInput(s: string)
{
  |s| == 19 && 
  |s| >= 2 && s[5] == ',' && s[13] == ',' &&
  forall i :: 0 <= i < |s| ==> (s[i] == ',' || ('a' <= s[i] <= 'z'))
}

function CommasToSpaces(s: string): string
  requires ValidInput(s)
{
  seq(|s|, i requires 0 <= i < |s| => if s[i] == ',' then ' ' else s[i])
}

predicate CorrectOutput(s: string, result: string)
  requires ValidInput(s)
{
  |result| == |s| + 1 &&
  result[|result| - 1] == '\n' &&
  forall i :: 0 <= i < |s| ==> 
    (s[i] == ',' ==> result[i] == ' ') &&
    (s[i] != ',' ==> result[i] == s[i])
}

// <vc-helpers>
lemma lemma_CommasToSpaces_length(s: string)
  requires ValidInput(s)
  ensures |CommasToSpaces(s)| == |s|
{
  // The definition of CommasToSpaces uses seq(|s|, ...), which directly implies the length.
  // Dafny's type system handles this implicitly for simple seq definitions.
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
  requires ValidInput(s)
  ensures CorrectOutput(s, result)
// </vc-spec>
// <vc-code>
{
  var temp_result := CommasToSpaces(s);

  // Prove that CommasToSpaces preserves characters not equal to ','
  forall i | 0 <= i < |s| && s[i] != ','
    ensures temp_result[i] == s[i]
  {
      calc {
        temp_result[i];
        (seq(|s|, j requires 0 <= j < |s| => if s[j] == ',' then ' ' else s[j]))[i];
        if s[i] == ',' then ' ' else s[i];
      }
      assert (if s[i] == ',' then ' ' else s[i]) == s[i]; // Since s[i] != ','
  }

  // Prove that CommasToSpaces changes ',' to ' '
  forall i | 0 <= i < |s| && s[i] == ','
    ensures temp_result[i] == ' '
  {
      calc {
        temp_result[i];
        (seq(|s|, j requires 0 <= j < |s| => if s[j] == ',' then ' ' else s[j]))[i];
        if s[i] == ',' then ' ' else s[i];
      }
      assert (if s[i] == ',' then ' ' else s[i]) == ' '; // Since s[i] == ','
  }

  result := temp_result + "\n";
  
  // Post-condition: |result| == |s| + 1
  lemma_CommasToSpaces_length(s);
  assert |temp_result| == |s|;
  assert |result| == |temp_result| + 1; // String concatenation property
  assert |result| == |s| + 1;

  // Post-condition: result[|result| - 1] == '\n'
  assert result[|result| - 1] == '\n'; // String concatenation property

  // Post-condition: forall i :: 0 <= i < |s| ==> (s[i] == ',' ==> result[i] == ' ') && (s[i] != ',' ==> result[i] == s[i])
  forall i | 0 <= i < |s|
    ensures (s[i] == ',' ==> result[i] == ' ') && (s[i] != ',' ==> result[i] == s[i])
  {
    assert i < |result|; // To show result[i] is defined
    if s[i] == ',' {
      assert temp_result[i] == ' '; // From the proof above for ','
      assert result[i] == temp_result[i]; // By definition of concatenation at index i < |temp_result|
      assert result[i] == ' ';
    } else {
      assert temp_result[i] == s[i]; // From the proof above for != ','
      assert result[i] == temp_result[i]; // By definition of concatenation at index i < |temp_result|
      assert result[i] == s[i];
    }
  }
}
// </vc-code>

