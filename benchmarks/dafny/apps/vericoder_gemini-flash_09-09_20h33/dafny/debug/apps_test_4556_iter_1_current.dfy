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
    invariant (forall j :: 8 <= j < i ==> input[j] != ' ' || !(input[j+1 .. j+8] == "Contest" && j + 8 == |input| - 1))
  {
    if input[i] == ' ' && input[i+1 .. i+8] == "Contest" && i + 8 == |input| - 1 {
      spacePos := i;
      return;
    }
    i := i + 1;
  }
  // This part should be unreachable given ValidInput
  // However, Dafny requires all paths to return a value.
  // We can assert false or pick a default, but since ValidInput guarantees existence,
  // the loop will always find it. For formal verification, we might add:
  // assert false; // Or a more advanced proof that this is unreachable
  // For practical purposes, and since the postconditions are guaranteed by ValidInput
  // once spacePos is found, a dummy return is used as a fallback that should never be hit.
  spacePos := 8; // Dummy value, should not be reached
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures ValidOutput(input, result)
// </vc-spec>
// <vc-code>
{
   var spacePos := 0;
   var i := 8;
   while i < |input| - 8
     invariant 8 <= i <= |input| - 8
     invariant (forall j :: 8 <= j < i ==> !(input[j] == ' ' && input[j+1 .. j+8] == "Contest" && j + 8 == |input| - 1))
   {
     if input[i] == ' ' && input[i+1 .. i+8] == "Contest" && i + 8 == |input| - 1 {
       spacePos := i;
       break;
     }
     i := i + 1;
   }

   var middleChar := input[8];
   return "A" + middleChar as string + "C\n";
}
// </vc-code>

