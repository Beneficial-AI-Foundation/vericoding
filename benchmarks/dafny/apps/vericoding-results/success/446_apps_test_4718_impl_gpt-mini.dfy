predicate ValidInput(dateStr: string) 
{
    |dateStr| == 10 && dateStr[0..4] == "2017"
}

predicate ValidOutput(input: string, output: string)
    requires |input| >= 4
{
    output == "2018" + input[4..] &&
    |output| == 10 &&
    output[0..4] == "2018" &&
    output[4..] == input[4..]
}

// <vc-helpers>
// No helper lemmas required for this simple string manipulation.
// </vc-helpers>

// <vc-spec>
method solve(dateStr: string) returns (result: string)
    requires ValidInput(dateStr)
    ensures ValidOutput(dateStr, result)
// </vc-spec>
// <vc-code>
{
  var suffix := dateStr[4..];
  result := "2018" + suffix;
  assert result == "2018" + dateStr[4..];
  assert |dateStr| == 10;
  assert |suffix| == |dateStr| - 4;
  assert |result| == | "2018" | + |suffix|;
  assert | "2018" | == 4;
  assert |result| == 10;
  assert result[0..4] == "2018";
  assert result[4..] == dateStr[4..];
}
// </vc-code>

