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

// <vc-helpers>
lemma ProcessStringEquivalence(input: string, stack: seq<char>)
    ensures ProcessString(input, stack) == ProcessStringIterative(input, stack)
{
    // This lemma establishes that the recursive and iterative versions are equivalent
}

function ProcessStringIterative(input: string, stack: seq<char>): seq<char>
{
    ProcessString(input, stack)
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    ensures result == "Yes\n" || result == "No\n"
    ensures result == "Yes\n" <==> StackAlgorithmResultsInEmptyStack(ExtractFirstLine(input))
// </vc-spec>
// <vc-code>
{
    var firstLine := "";
    var i := 0;
    
    // Extract first line
    while i < |input| && input[i] != '\n'
        invariant 0 <= i <= |input|
        invariant firstLine == ExtractFirstLine(input[..i])
    {
        firstLine := firstLine + [input[i]];
        i := i + 1;
    }
    
    // Process the first line with stack algorithm
    var stack: seq<char> := [];
    var j := 0;
    
    while j < |firstLine|
        invariant 0 <= j <= |firstLine|
        invariant stack == ProcessString(firstLine[..j], [])
    {
        var c := firstLine[j];
        if |stack| > 0 && stack[|stack| - 1] == c {
            stack := stack[..|stack| - 1];
        } else {
            stack := stack + [c];
        }
        j := j + 1;
    }
    
    if |stack| == 0 {
        result := "Yes\n";
    } else {
        result := "No\n";
    }
}
// </vc-code>

