predicate ValidInput(input: string)
{
    |input| > 0 &&
    input[|input|-1] == '\n' &&
    |input| >= 2 &&
    (forall i :: 0 <= i < |input|-1 ==> '0' <= input[i] <= '9') &&
    (input[0] != '0' || |input| == 2)
}

function MaxDivisibleBy3Segments(s: string): int
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures MaxDivisibleBy3Segments(s) >= 0
    ensures MaxDivisibleBy3Segments(s) <= |s|
{
    MaxDivisibleBy3SegmentsHelper(s, 0, "", 0)
}

// <vc-helpers>
function MaxDivisibleBy3SegmentsHelper(s: string, index: int, currentSumStr: string, count: int): int
  requires 0 <= index <= |s|
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  requires currentSumStr == "" || (currentSumStr != "" && (currentSumStr as int) >= 0)
  ensures MaxDivisibleBy3SegmentsHelper(s, index, currentSumStr, count) >= count
{
  if index == |s| then
    if currentSumStr != "" && (currentSumStr as int) % 3 == 0 then
      count + 1
    else
      count
  else
    var include_val := 0;
    if currentSumStr != "" && (currentSumStr as int) % 3 == 0 then
      include_val := MaxDivisibleBy3SegmentsHelper(s, index + 1, "" + s[index], count + 1);
    else
      include_val := MaxDivisibleBy3SegmentsHelper(s, index + 1, currentSumStr + s[index], count);
    
    var exclude_val := MaxDivisibleBy3SegmentsHelper(s, index + 1, "" + s[index], count);

    max(include_val, exclude_val)
}

function IntToString(n: int): string
  requires n >= 0
  ensures (n == 0) ==> (IntToString(n) == "0")
  ensures (n > 0) ==> (|IntToString(n)| > 0 && (IntToString(n) as int) == n)
{
  if n == 0 then "0"
  else
    var s := "";
    var temp := n;
    while temp > 0
      invariant temp >= 0
      invariant (s == "" || (s as int) >= 0)
      decreases temp
    {
      s := (temp % 10 as char) + s;
      temp := temp / 10;
    }
    s
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures |result| > 0
    ensures result[|result|-1] == '\n'
    ensures exists count :: 0 <= count <= |input|-1 && result == IntToString(count) + "\n"
    ensures exists count :: count == MaxDivisibleBy3Segments(input[0..|input|-1]) && result == IntToString(count) + "\n"
// </vc-spec>
// <vc-code>
{
  var trimmedInput := input[0..|input|-1]; // Remove the trailing newline
  var count := MaxDivisibleBy3Segments(trimmedInput);
  result := IntToString(count) + "\n";
}
// </vc-code>

