predicate ValidInput(input: string)
{
    && |input| >= 18  // Minimum: "AtCoder X Contest\n"
    && input[|input| - 1] == '\n'  // Input ends with newline
    && input[0..7] == "AtCoder"
    && input[7] == ' '
    && exists spacePos :: 8 <= spacePos < |input| - 8 && input[spacePos] == ' ' && 
       input[spacePos + 1..spacePos + 8] == "Contest" &&
       spacePos + 8 == |input| - 1
    && exists spacePos :: 8 <= spacePos < |input| - 8 && input[spacePos] == ' ' && 
       spacePos > 8 &&  // Middle word is non-empty
       'A' <= input[8] <= 'Z' &&  // First char is uppercase
       (forall k :: 9 <= k < spacePos ==> 'a' <= input[k] <= 'z')  // Rest are lowercase
}

predicate ValidOutput(input: string, result: string)
{
    && |result| == 4  // "AxC\n" format
    && result[0] == 'A'
    && result[2] == 'C'
    && result[3] == '\n'
    && exists spacePos :: 8 <= spacePos < |input| - 8 && input[spacePos] == ' ' && 
       result[1] == input[8]  // Second char is first char of middle word
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures ValidOutput(input, result)
// </vc-spec>
// <vc-code>
{
  ghost var sp :| 8 <= sp < |input| - 8 && input[sp] == ' ' &&
                   input[sp + 1..sp + 8] == "Contest" &&
                   sp + 8 == |input| - 1;

  var mid := input[8..9];
  var r1 := "A" + mid;
  result := r1 + "C\n";

  assert |mid| == 1;
  assert |r1| == 2;
  assert r1[0] == 'A';
  assert r1[1] == mid[0];
  assert mid[0] == input[8];

  assert |result| == 4;
  assert result[0] == r1[0];
  assert result[1] == r1[1];
  assert result[2] == 'C';
  assert result[3] == '\n';

  assert exists s :: 8 <= s < |input| - 8 && input[s] == ' ' && result[1] == input[8];
}
// </vc-code>

