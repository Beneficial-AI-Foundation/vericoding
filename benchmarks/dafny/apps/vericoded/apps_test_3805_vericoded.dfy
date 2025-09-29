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
lemma ExtractFirstLinePrefix(input: string, i: int)
    requires 0 <= i <= |input|
    requires forall k :: 0 <= k < i ==> input[k] != '\n'
    ensures ExtractFirstLine(input[..i]) == input[..i]
{
    if i == 0 {
        assert input[..0] == "";
        assert ExtractFirstLine(input[..0]) == ExtractFirstLine("") == "";
    } else {
        assert input[..i-1] == input[..i][..i-1];
        assert forall k :: 0 <= k < i-1 ==> input[k] != '\n';
        ExtractFirstLinePrefix(input, i-1);
        assert ExtractFirstLine(input[..i-1]) == input[..i-1];
        
        assert input[..i][0] == input[0];
        assert input[0] != '\n';
        assert input[..i][1..] == input[1..i];
        assert ExtractFirstLine(input[..i]) == [input[0]] + ExtractFirstLine(input[..i][1..]);
        assert input[..i][1..] == input[1..i];
        
        if i == 1 {
            assert input[1..i] == input[1..1] == "";
            assert input[..i-1] == input[..0] == "";
            assert ExtractFirstLine(input[1..1]) == "";
            assert ExtractFirstLine(input[..i]) == [input[0]] + "";
            assert [input[0]] == input[..1];
            assert input[..i] == input[..1];
        } else {
            assert i > 1;
            assert input[1..i] == input[1..][..i-1];
            ExtractFirstLinePrefix(input[1..], i-1);
            assert ExtractFirstLine(input[1..i]) == input[1..i];
        }
        
        assert ExtractFirstLine(input[..i]) == [input[0]] + ExtractFirstLine(input[1..i]);
        if i == 1 {
            assert ExtractFirstLine(input[1..i]) == "";
            assert ExtractFirstLine(input[..i]) == [input[0]];
            assert input[..i] == [input[0]];
        } else {
            assert ExtractFirstLine(input[1..i]) == input[1..i];
            assert ExtractFirstLine(input[..i]) == [input[0]] + input[1..i];
            assert [input[0]] + input[1..i] == input[..i];
        }
    }
}

lemma ExtractFirstLineWithNewline(input: string, i: int)
    requires 0 <= i < |input|
    requires input[i] == '\n'
    requires forall k :: 0 <= k < i ==> input[k] != '\n'
    ensures ExtractFirstLine(input) == input[..i]
{
    if i == 0 {
        assert input[0] == '\n';
        assert ExtractFirstLine(input) == "";
        assert input[..0] == "";
    } else {
        assert input[0] != '\n';
        assert ExtractFirstLine(input) == [input[0]] + ExtractFirstLine(input[1..]);
        ExtractFirstLineWithNewline(input[1..], i-1);
        assert ExtractFirstLine(input[1..]) == input[1..i];
        assert ExtractFirstLine(input) == [input[0]] + input[1..i];
        assert [input[0]] + input[1..i] == input[..i];
    }
}

lemma ExtractFirstLineComplete(input: string)
    requires |input| > 0
    requires exists k :: 0 <= k < |input| && input[k] == '\n'
    ensures var k := FindNewline(input); ExtractFirstLine(input) == input[..k]
{
    var k := FindNewline(input);
    ExtractFirstLinePrefix(input, k);
    assert input[..k] + input[k..] == input;
    assert input[k] == '\n';
}

function FindNewline(input: string): int
    requires |input| > 0
    requires exists k :: 0 <= k < |input| && input[k] == '\n'
    ensures 0 <= FindNewline(input) < |input|
    ensures input[FindNewline(input)] == '\n'
    ensures forall j :: 0 <= j < FindNewline(input) ==> input[j] != '\n'
{
    if input[0] == '\n' then 0
    else 1 + FindNewline(input[1..])
}

lemma ExtractFirstLineNoNewline(input: string)
    requires forall k :: 0 <= k < |input| ==> input[k] != '\n'
    ensures ExtractFirstLine(input) == input
{
    if |input| == 0 {
    } else {
        ExtractFirstLineNoNewline(input[1..]);
    }
}

lemma ProcessStringStep(input: string, j: int, stack: seq<char>)
    requires 0 <= j < |input|
    ensures ProcessString(input[..j+1], []) == 
            (var tempStack := ProcessString(input[..j], []);
             var c := input[j];
             if |tempStack| > 0 && tempStack[|tempStack| - 1] == c 
             then tempStack[..|tempStack| - 1] 
             else tempStack + [c])
{
    assert input[..j+1] == input[..j] + [input[j]];
    ProcessStringConcat(input[..j], [input[j]], []);
}

lemma ProcessStringConcat(s1: string, s2: string, stack: seq<char>)
    ensures ProcessString(s1 + s2, stack) == ProcessString(s2, ProcessString(s1, stack))
{
    if |s1| == 0 {
        assert s1 + s2 == s2;
    } else {
        assert (s1 + s2)[0] == s1[0];
        assert (s1 + s2)[1..] == s1[1..] + s2;
        var c := s1[0];
        var newStack := if |stack| > 0 && stack[|stack| - 1] == c 
                       then stack[..|stack| - 1] 
                       else stack + [c];
        ProcessStringConcat(s1[1..], s2, newStack);
    }
}

lemma ExtractFirstLineUpto(input: string, j: int)
    requires 0 <= j <= |input|
    requires forall k :: 0 <= k < j ==> input[k] != '\n'
    ensures ExtractFirstLine(input[..j]) == input[..j]
{
    ExtractFirstLinePrefix(input, j);
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
        invariant forall k :: 0 <= k < i ==> input[k] != '\n'
        invariant firstLine == input[..i]
        invariant firstLine == ExtractFirstLine(input[..i])
    {
        ExtractFirstLinePrefix(input, i);
        firstLine := firstLine + [input[i]];
        i := i + 1;
        ExtractFirstLinePrefix(input, i);
    }
    
    // Establish that firstLine == ExtractFirstLine(input)
    if i < |input| {
        assert input[i] == '\n';
        assert forall k :: 0 <= k < i ==> input[k] != '\n';
        ExtractFirstLineWithNewline(input, i);
        assert ExtractFirstLine(input) == input[..i];
        assert firstLine == input[..i];
        assert firstLine == ExtractFirstLine(input);
    } else {
        assert i == |input|;
        assert forall k :: 0 <= k < |input| ==> input[k] != '\n';
        ExtractFirstLineNoNewline(input);
        assert firstLine == input[..i];
        assert input[..i] == input;
        assert firstLine == ExtractFirstLine(input);
    }
    
    // Process the first line with stack algorithm
    var stack: seq<char> := [];
    var j := 0;
    
    while j < |firstLine|
        invariant 0 <= j <= |firstLine|
        invariant stack == ProcessString(firstLine[..j], [])
    {
        ProcessStringStep(firstLine, j, stack);
        var c := firstLine[j];
        if |stack| > 0 && stack[|stack| - 1] == c {
            stack := stack[..|stack| - 1];
        } else {
            stack := stack + [c];
        }
        j := j + 1;
    }
    
    assert firstLine[..j] == firstLine;
    assert stack == ProcessString(firstLine, []);
    assert firstLine == ExtractFirstLine(input);
    assert stack == ProcessString(ExtractFirstLine(input), []);
    assert |stack| == 0 <==> StackAlgorithmResultsInEmptyStack(ExtractFirstLine(input));
    
    if |stack| == 0 {
        result := "Yes\n";
    } else {
        result := "No\n";
    }
}
// </vc-code>

