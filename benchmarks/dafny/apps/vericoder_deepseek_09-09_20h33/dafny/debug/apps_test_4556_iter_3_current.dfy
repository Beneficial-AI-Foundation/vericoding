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
predicate ValidInput_Internal(input: string, spacePos: nat)
{
    8 <= spacePos < |input| - 8 &&
    input[spacePos] == ' ' &&
    input[spacePos + 1..spacePos + 8] == "Contest" &&
    spacePos + 8 == |input| - 1 &&
    spacePos > 8 &&
    'A' <= input[8] <= 'Z' &&
    (forall k :: 9 <= k < spacePos ==> 'a' <= input[k] <= 'z')
}

lemma ValidInput_ExtractSpacePos(input: string)
    requires ValidInput(input)
    ensures exists spacePos :: ValidInput_Internal(input, spacePos)
{
}

function ExtractMiddleChar(input: string, spacePos: nat): char
    requires ValidInput_Internal(input, spacePos)
{
    input[8]
}

predicate ValidOutput_Internal(input: string, result: string, spacePos: nat)
{
    |result| == 4 &&
    result[0] == 'A' &&
    result[2] == 'C' &&
    result[3] == '\n' &&
    result[1] == input[8]
}

lemma ValidOutput_FromSpacePos(input: string, result: string, spacePos: nat)
    requires ValidInput_Internal(input, spacePos) && result == "A" + [input[8]] + "C\n"
    ensures ValidOutput_Internal(input, result, spacePos)
{
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures ValidOutput(input, result)
// </vc-spec>
// <vc-code>
{
  ValidInput_ExtractSpacePos(input);
  var spacePos :| ValidInput_Internal(input, spacePos);
  var middleChar := ExtractMiddleChar(input, spacePos);
  result := "A" + [middleChar] + "C\n";
  ValidOutput_FromSpacePos(input, result, spacePos);
}
// </vc-code>

