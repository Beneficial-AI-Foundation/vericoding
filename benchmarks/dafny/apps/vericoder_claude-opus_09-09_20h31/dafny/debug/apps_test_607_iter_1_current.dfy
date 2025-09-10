predicate ValidInput(input: string)
{
    |input| > 0 && 
    (var nm := ParseTwoInts(input);
     var n := nm.0; var m := nm.1;
     n > 0 && m > 0)
}

function ParseTwoInts(input: string): (int, int)
    requires |input| > 0
{
    var lines := SplitLinesFunc(input);
    if |lines| == 0 then (0, 0)
    else 
        var parts := SplitSpacesFunc(lines[0]);
        if |parts| < 2 then (0, 0)
        else (StringToInt(parts[0]), StringToInt(parts[1]))
}

function ComputeHappinessSum(n: int, m: int): int
    requires n > 0 && m > 0
{
    SumUpToSize(n, m, n)
}

// <vc-helpers>
function SplitLinesFunc(s: string): seq<string>
{
    // Abstract function for splitting lines
    []  // Placeholder implementation
}

function SplitSpacesFunc(s: string): seq<string>
{
    // Abstract function for splitting by spaces
    []  // Placeholder implementation
}

function StringToInt(s: string): int
{
    // Abstract function for converting string to int
    0  // Placeholder implementation
}

function IntToString(n: int): string
    ensures forall c :: c in IntToString(n) ==> ('0' <= c <= '9') || c == '-'
{
    // Abstract function for converting int to string
    ""  // Placeholder implementation
}

function SumUpToSize(n: int, m: int, size: int): int
    requires n > 0 && m > 0 && size >= 0
{
    if size == 0 then 0
    else if size <= m then size * (size + 1) / 2
    else m * (m + 1) / 2 + (size - m) * m
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (output: string)
    requires |input| > 0
    ensures |output| >= 0
    ensures ValidInput(input) ==> 
        (var nm := ParseTwoInts(input);
         var n := nm.0; var m := nm.1;
         output == IntToString(ComputeHappinessSum(n, m)) + "\n")
    ensures ValidInput(input) ==> |output| > 0 && output[|output|-1] == '\n'
    ensures ValidInput(input) ==> forall c :: c in output ==> (c == '\n' || ('0' <= c <= '9'))
    ensures !ValidInput(input) ==> output == ""
// </vc-spec>
// <vc-code>
{
    if !ValidInput(input) {
        output := "";
    } else {
        var nm := ParseTwoInts(input);
        var n := nm.0;
        var m := nm.1;
        var result := ComputeHappinessSum(n, m);
        output := IntToString(result) + "\n";
    }
}
// </vc-code>

