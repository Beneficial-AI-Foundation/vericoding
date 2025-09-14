predicate ValidInput(input: string)
{
    |input| > 0 && 
    (input[0] == '0' || input[0] == '1') && 
    (|input| == 1 || (|input| > 1 && input[1] == '\n'))
}

function LogicalNot(digit: char): string
    requires digit == '0' || digit == '1'
{
    if digit == '0' then "1\n" else "0\n"
}

predicate CorrectOutput(input: string, output: string)
    requires ValidInput(input)
{
    output == LogicalNot(input[0])
}

// <vc-helpers>
lemma LogicalNotCorrect(digit: char, s: string)
  requires digit == '0' || digit == '1'
  requires s == LogicalNot(digit)
  ensures (digit == '0' && s == "1\n") || (digit == '1' && s == "0\n")
{
  if digit == '0' {
    assert s == "1\n";
  } else {
    assert s == "0\n";
  }
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (output: string)
    requires ValidInput(input)
    ensures CorrectOutput(input, output)
// </vc-spec>
// <vc-code>
{
    if input[0] == '0' {
        output := "1\n";
        assert CorrectOutput(input, output); // Added for verification
    } else {
        output := "0\n";
        assert CorrectOutput(input, output); // Added for verification
    }
}
// </vc-code>

