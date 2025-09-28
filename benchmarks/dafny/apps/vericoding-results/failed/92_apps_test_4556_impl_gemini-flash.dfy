// <vc-preamble>
predicate ValidInput(input: string)
{
    && |input| >= 18
    && input[|input| - 1] == '\n'
    && input[0..7] == "AtCoder"
    && input[7] == ' '
    && exists spacePos :: 8 <= spacePos < |input| - 8 && input[spacePos] == ' ' && 
       input[spacePos + 1..spacePos + 8] == "Contest" &&
       spacePos + 8 == |input| - 1
    && exists spacePos :: 8 <= spacePos < |input| - 8 && input[spacePos] == ' ' && 
       spacePos > 8 &&
       'A' <= input[8] <= 'Z' &&
       (forall k :: 9 <= k < spacePos ==> 'a' <= input[k] <= 'z')
}

predicate ValidOutput(input: string, result: string)
{
    && |result| == 4
    && result[0] == 'A'
    && result[2] == 'C'
    && result[3] == '\n'
    && exists spacePos :: 8 <= spacePos < |input| - 8 && input[spacePos] == ' ' && 
       result[1] == input[8]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The `ValidInput` predicate ensures that such a space must exist. */
lemma GetSpacePosition(input: string) returns (spacePos: int)
    requires ValidInput(input)
    ensures 8 <= spacePos < |input| - 8 && input[spacePos] == ' ' && input[spacePos + 1 .. spacePos + 8] == "Contest"
{
    var i := 8;
    while i < |input| - 8
        invariant 8 <= i <= |input| - 8
        invariant forall k :: 8 <= k < i ==> !(input[k] == ' ' && input[k + 1 .. k + 8] == "Contest")
    {
        if input[i] == ' ' && input[i + 1 .. i + 8] == "Contest"
        {
            spacePos := i;
            return;
        }
        i := i + 1;
    }
    // The loop must terminate and find a spacePos due to ValidInput precondition.
    // Proof of existence from ValidInput predicate ensures termination.
    assert false; // This line should be unreachable
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures ValidOutput(input, result)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected type mismatch in string concatenation by converting char to string. */
{
  var spacePos := GetSpacePosition(input);
  var charToTake := input[8];
  result := "A" + charToTake as string + "C\n";
}
// </vc-code>
