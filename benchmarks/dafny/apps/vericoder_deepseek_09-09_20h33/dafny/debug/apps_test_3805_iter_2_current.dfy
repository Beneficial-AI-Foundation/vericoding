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
lemma ExtractFirstLineLemma(s: string)
    ensures |ExtractFirstLine(s)| <= |s|
    decreases |s|
{
    if |s| != 0 && s[0] != '\n' {
        ExtractFirstLineLemma(s[1..]);
    }
}

lemma ProcessStringDecreases(s: string, stack: seq<char>)
    ensures |ProcessString(s, stack)| <= |s| + |stack|
    decreases |s|
{
    if |s| > 0 {
        var c := s[0];
        var newStack := if |stack| > 0 && stack[|stack| - 1] == c 
                       then stack[..|stack| - 1] 
                       else stack + [c];
        ProcessStringDecreases(s[1..], newStack);
    }
}

lemma ProcessStringEquivalent(s: string, stack: seq<char>)
    ensures ProcessString(s, stack) == (
        if |s| == 0 then stack
        else
            var c := s[0];
            var newStack := if |stack| > 0 && stack[|stack| - 1] == c 
                          then stack[..|stack| - 1] 
                          else stack + [c];
            ProcessString(s[1..], newStack)
    )
{
    // This lemma ensures the function definition is transparent to the verifier
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    ensures result == "Yes\n" || result == "No\n"
    ensures result == "Yes\n" <==> StackAlgorithmResultsInEmptyStack(ExtractFirstLine(input))
// </vc-spec>
// <vc-code>
{
    var firstLine := ExtractFirstLine(input);
    var stack : seq<char> := [];
    var i := 0;
    
    while i < |firstLine|
        invariant 0 <= i <= |firstLine|
        invariant stack == ProcessString(firstLine[..i], [])
        decreases |firstLine| - i
    {
        var c := firstLine[i];
        var oldStack := stack;
        
        if |stack| > 0 && stack[|stack| - 1] == c {
            stack := stack[..|stack| - 1];
        } else {
            stack := stack + [c];
        }
        
        // Prove that the updated stack matches the functional definition
        assert stack == ProcessString(firstLine[..i] + [c], []) by {
            ProcessStringEquivalent(firstLine[..i] + [c], []);
            assert ProcessString(firstLine[..i] + [c], []) ==
                (if |stack| > 0 && oldStack[|oldStack| - 1] == c 
                 then oldStack[..|oldStack| - 1]
                 else oldStack + [c]);
        }
        
        i := i + 1;
    }
    
    // Now we know stack == ProcessString(firstLine, [])
    assert stack == ProcessString(firstLine, []);
    
    if |stack| == 0 {
        result := "Yes\n";
    } else {
        result := "No\n";
    }
}
// </vc-code>

