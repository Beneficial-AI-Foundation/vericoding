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

lemma ProcessStringPrefixLemma(s: string, stack: seq<char>)
    requires |s| > 0
    ensures ProcessString(s, stack) == ProcessString(s[1..], 
        if |stack| > 0 && stack[|stack| - 1] == s[0] 
        then stack[..|stack| - 1] 
        else stack + [s[0]])
{
}

lemma ProcessStringCharByChar(input: string, stack: seq<char>, i: nat, c: char)
    requires i < |input|
    requires stack == ProcessString(input[..i], [])
    ensures ProcessString(input[..i] + [c], []) == 
        (if |stack| > 0 && stack[|stack| - 1] == c 
         then stack[..|stack| - 1] 
         else stack + [c])
{
    calc {
        ProcessString(input[..i] + [c], []);
        == { ProcessStringEquivalent(input[..i] + [c], []); }
        (if |input[..i] + [c]| == 0 then []
        else
            var char0 := (input[..i] + [c])[0];
            var newStack0 := if |[]| > 0 && [][|[]| - 1] == char0 
                           then [][..|[]| - 1] 
                           else [] + [char0];
            ProcessString((input[..i] + [c])[1..], newStack0));
        == // Simplify
        ProcessString(input[..i], [c]);
    };
    
    calc {
        ProcessString(input[..i], [c]);
        == { ProcessStringEquivalent(input[..i], [c]); }
        (if |input[..i]| == 0 then [c]
        else
            var char1 := input[..i][0];
            var newStack1 := if |[c]| > 0 && [c][|[c]| - 1] == char1 
                           then [c][..|[c]| - 1] 
                           else [c] + [char1];
            ProcessString(input[..i][1..], newStack1));
    };
    
    // Use the fact that stack == ProcessString(input[..i], [])
    // and show the recursive structure matches the if-else logic
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
        ProcessStringCharByChar(firstLine, oldStack, i, c);
        
        i := i + 1;
    }
    
    // Now we know stack == ProcessString(firstLine, [])
    if |stack| == 0 {
        result := "Yes\n";
    } else {
        result := "No\n";
    }
}
// </vc-code>

