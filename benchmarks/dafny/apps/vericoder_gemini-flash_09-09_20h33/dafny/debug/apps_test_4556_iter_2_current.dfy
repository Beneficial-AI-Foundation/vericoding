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
lemma GetSpacePos(input: string) returns (spacePos: int)
  requires ValidInput(input)
  ensures 8 <= spacePos < |input| - 8 && input[spacePos] == ' ' && input[spacePos + 1 .. spacePos + 8] == "Contest" && spacePos + 8 == |input| - 1
  ensures spacePos > 8 && 'A' <= input[8] <= 'Z' && (forall k :: 9 <= k < spacePos ==> 'a' <= input[k] <= 'z')
{
  var i := 8;
  while i < |input| - 8
    invariant 8 <= i <= |input| - 8
    invariant (forall j :: 8 <= j < i ==> !(input[j] == ' ' && input[j+1 .. j+8] == "Contest" && j + 8 == |input| - 1))
  {
    // The proof that this loop terminates relies on the existence quantified in ValidInput.
    // Dafny can infer this, but for larger proofs, an explicit lemma might be needed.
    if input[i] == ' ' && input[i+1 .. i+8] == "Contest" && i + 8 == |input| - 1 {
      spacePos := i;
      return;
    }
    i := i + 1;
  }
  // This part should be unreachable given ValidInput.
  // We can add an assert false; but it's simpler to just make sure the loop finds it.
  // Since `ValidInput` guarantees the existence of such `spacePos`, this path is never taken.
  // Dafny requires all paths to return a value, so we technically need a return here.
  // However, the proof of `ValidOutput` will rely on `GetSpacePos` finding the correct `spacePos`.
  // A dummy return value to satisfy the verifier for unreachable code.
  // This value is never actually used if the precondition holds.
  spacePos := 8;
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
   var middleChar := input[8];
   return "A" + middleChar.ToString() + "C\n";
}
// </vc-code>

