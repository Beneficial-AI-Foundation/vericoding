// <vc-preamble>
function ExtractFirstLine(input: string): string
{
    if |input| == 0 then ""
    else if input[0] == '\n' then ""
    else 
        var rest := ExtractFirstLine(input[1..]);
        [input[0]] + rest
}

function ProcessString(input: string, stack: seq<char>): seq<char>
{
    if |input| == 0 then stack
    else
        var c := input[0];
        var newStack := if |stack| > 0 && stack[|stack| - 1] == c 
                       then stack[..|stack| - 1] 
                       else stack + [c];
        ProcessString(input[1..], newStack)
}

predicate StackAlgorithmResultsInEmptyStack(input: string)
{
    var stack := ProcessString(input, []);
    |stack| == 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Removed 'entails' clause from function signature due to compilation error, as it's not supported for functions. The functionality is implicitly handled by the ExtractFirstLine definition. Added correct base cases. */
function FirstLine(input: string): string
{
    if |input| == 0 then ""
    else if input[0] == '\n' then ""
    else if |input| > 0 && input[0] != '\n' then [input[0]] + FirstLine(input[1..])
    else ""
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    ensures result == "Yes\n" || result == "No\n"
    ensures result == "Yes\n" <==> StackAlgorithmResultsInEmptyStack(ExtractFirstLine(input))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Ensured if/else syntax is correct by adding braces */
{
  var firstLine := ExtractFirstLine(input);
  var isEmpty := StackAlgorithmResultsInEmptyStack(firstLine);
  if isEmpty {
    result := "Yes\n";
  } else {
    result := "No\n";
  }
}
// </vc-code>
