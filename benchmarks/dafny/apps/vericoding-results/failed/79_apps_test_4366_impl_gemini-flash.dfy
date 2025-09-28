// <vc-preamble>
predicate ValidInput(input: string)
{
    exists A, B :: 0 <= A <= 23 && 0 <= B <= 23 && 
    (input == IntToString(A) + " " + IntToString(B) + "\n" ||
     input == IntToString(A) + " " + IntToString(B))
}

function ContestStartTime(A: int, B: int): int
    requires 0 <= A <= 23 && 0 <= B <= 23
    ensures 0 <= ContestStartTime(A, B) <= 23
{
    (A + B) % 24
}

predicate CorrectOutput(input: string, result: string)
    requires ValidInput(input)
{
    exists A, B :: 0 <= A <= 23 && 0 <= B <= 23 && 
    (input == IntToString(A) + " " + IntToString(B) + "\n" ||
     input == IntToString(A) + " " + IntToString(B)) &&
    result == IntToString(ContestStartTime(A, B)) + "\n"
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Corrected signature for GetNumbers by specifying return type of `a` and `b`. Added ensures clauses. */
function GetNumbers(input: string) : (a: int, b: int)
  requires ValidInput(input)
  ensures 0 <= a <= 23 && 0 <= b <= 23
{
  var parts := input.Split(' ');
  var A_str := parts[0];
  var B_str := parts[1].Substring(0, parts[1].Length - (if parts[1].EndsWith("\n") then 1 else 0));

  var a_res := StringToInt(A_str);
  var b_res := StringToInt(B_str);

  return (a_res, b_res);
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    requires ValidInput(input)
    ensures CorrectOutput(input, result)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed `GetNumbers` call and `result` assignment. */
{
  var a, b := GetNumbers(input);
  var startTime := ContestStartTime(a, b);
  result := IntToString(startTime) + "\n";
}
// </vc-code>
