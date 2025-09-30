predicate ValidInput(input: string) {
    |input| >= 0
}

predicate ValidTestCase(n: int, a: int, b: int, c: int, d: int) {
    n >= 1 && n <= 1000 &&
    a >= 0 && a <= 1000 &&
    b >= 0 && b < a &&
    c >= 0 && c <= 1000 &&
    d >= 0 && d < c
}

function CanAchieveWeight(n: int, a: int, b: int, c: int, d: int): bool {
    var minWeight := (a - b) * n;
    var maxWeight := (a + b) * n;
    var targetMin := c - d;
    var targetMax := c + d;
    !(minWeight > targetMax || maxWeight < targetMin)
}

predicate ValidOutput(output: string) {
    forall i :: 0 <= i < |output| ==> output[i] in "YesNo\n"
}

// <vc-helpers>
method parseInt(s: string, start: int) returns (value: int, nextPos: int)
    requires 0 <= start <= |s|
    ensures start <= nextPos <= |s|
{
    var pos := start;
    // Skip whitespace
    while pos < |s| && s[pos] == ' '
        invariant start <= pos <= |s|
    {
        pos := pos + 1;
    }
    
    value := 0;
    while pos < |s| && '0' <= s[pos] <= '9'
        invariant start <= pos <= |s|
    {
        value := value * 10 + (s[pos] - '0') as int;
        pos := pos + 1;
    }
    nextPos := pos;
}

method skipNewline(s: string, start: int) returns (nextPos: int)
    requires 0 <= start <= |s|
    ensures start <= nextPos <= |s|
{
    nextPos := start;
    if nextPos < |s| && s[nextPos] == '\n' {
        nextPos := nextPos + 1;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures ValidOutput(result)
    ensures (input == "" || input == "\n") ==> result == ""
    ensures input != "" && input != "\n" ==> (|result| > 0 ==> result[|result|-1] == '\n' || (|result| > 3 && result[|result|-4..] in ["Yes\n", "No\n"]))
// </vc-spec>
// <vc-code>
{
    if |input| == 0 || input == "\n" {
        return "";
    }
    
    var pos := 0;
    var t: int;
    t, pos := parseInt(input, pos);
    if t < 0 {
        t := 0;  // Ensure t is non-negative
    }
    pos := skipNewline(input, pos);
    
    result := "";
    var i := 0;
    
    while i < t && pos < |input|
        invariant 0 <= i <= t
        invariant 0 <= pos <= |input|
        invariant ValidOutput(result)
        invariant |result| > 0 ==> result[|result|-1] == '\n'
    {
        var n, a, b, c, d: int;
        
        n, pos := parseInt(input, pos);
        a, pos := parseInt(input, pos);
        b, pos := parseInt(input, pos);
        c, pos := parseInt(input, pos);
        d, pos := parseInt(input, pos);
        pos := skipNewline(input, pos);
        
        if CanAchieveWeight(n, a, b, c, d) {
            result := result + "Yes\n";
        } else {
            result := result + "No\n";
        }
        
        i := i + 1;
    }
}
// </vc-code>

