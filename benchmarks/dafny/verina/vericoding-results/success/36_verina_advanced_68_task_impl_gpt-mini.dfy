// <vc-preamble>
predicate IsDigit(c: char)
{
    '0' <= c <= '9'
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): replace ord with explicit digit mapping */
function DigitValue(c: char): int
  requires IsDigit(c)
{
  if c == '0' then 0
  else if c == '1' then 1
  else if c == '2' then 2
  else if c == '3' then 3
  else if c == '4' then 4
  else if c == '5' then 5
  else if c == '6' then 6
  else if c == '7' then 7
  else if c == '8' then 8
  else 9
}

/* helper modified by LLM (iteration 2): prove bounds for DigitValue */
lemma DigitValueBounds(c: char)
  requires IsDigit(c)
  ensures 0 <= DigitValue(c) <= 9
{
  if c == '0' {
    assert DigitValue(c) == 0;
  } else if c == '1' {
    assert DigitValue(c) == 1;
  } else if c == '2' {
    assert DigitValue(c) == 2;
  } else if c == '3' {
    assert DigitValue(c) == 3;
  } else if c == '4' {
    assert DigitValue(c) == 4;
  } else if c == '5' {
    assert DigitValue(c) == 5;
  } else if c == '6' {
    assert DigitValue(c) == 6;
  } else if c == '7' {
    assert DigitValue(c) == 7;
  } else if c == '8' {
    assert DigitValue(c) == 8;
  } else {
    assert DigitValue(c) == 9;
  }
  assert 0 <= DigitValue(c) <= 9;
}

// </vc-helpers>

// <vc-spec>
lemma RunLengthEncoderProperty(input: string, result: string)
    requires
        // Non-empty check: input is empty iff result is empty
        (|input| == 0) <==> (|result| == 0)
    requires
        // Format validation: result alternates between characters and digits
        |result| > 0 ==> (
            forall i :: 0 <= i < |result| ==> 
                (i % 2 == 0 ==> !IsDigit(result[i])) &&
                (i % 2 == 1 ==> IsDigit(result[i]))
        )
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): case analysis over result length to establish alternation property */
  if |result| == 0 {
    assert |input| == 0;
    return;
  }
  var i := 0;
  while i < |result|
    decreases |result| - i
  {
    assert (i % 2 == 0 ==> !IsDigit(result[i])) && (i % 2 == 1 ==> IsDigit(result[i]));
    i := i + 1;
  }
}

// </vc-code>
