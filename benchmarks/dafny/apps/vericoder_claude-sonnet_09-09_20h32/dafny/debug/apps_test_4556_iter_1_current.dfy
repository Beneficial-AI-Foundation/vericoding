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
lemma SpacePosExists(input: string)
    requires ValidInput(input)
    ensures exists spacePos :: 8 <= spacePos < |input| - 8 && input[spacePos] == ' ' && 
            input[spacePos + 1..spacePos + 8] == "Contest" &&
            spacePos + 8 == |input| - 1
{
    // This follows directly from ValidInput
}

lemma SpacePosUnique(input: string)
    requires ValidInput(input)
    ensures exists! spacePos :: 8 <= spacePos < |input| - 8 && input[spacePos] == ' ' && 
            input[spacePos + 1..spacePos + 8] == "Contest" &&
            spacePos + 8 == |input| - 1
{
    SpacePosExists(input);
    // Uniqueness follows from the constraint that spacePos + 8 == |input| - 1
}

function GetSpacePos(input: string): int
    requires ValidInput(input)
    ensures 8 <= GetSpacePos(input) < |input| - 8
    ensures input[GetSpacePos(input)] == ' '
    ensures input[GetSpacePos(input) + 1..GetSpacePos(input) + 8] == "Contest"
    ensures GetSpacePos(input) + 8 == |input| - 1
{
    SpacePosUnique(input);
    var spacePos :| 8 <= spacePos < |input| - 8 && input[spacePos] == ' ' && 
                   input[spacePos + 1..spacePos + 8] == "Contest" &&
                   spacePos + 8 == |input| - 1;
    spacePos
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures ValidOutput(input, result)
// </vc-spec>
// <vc-code>
{
    var spacePos := GetSpacePos(input);
    var middleWordFirstChar := input[8];
    result := "A" + [middleWordFirstChar] + "C\n";
}
// </vc-code>

