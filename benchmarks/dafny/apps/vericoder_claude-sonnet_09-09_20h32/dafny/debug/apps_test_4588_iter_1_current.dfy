predicate ValidInput(input: string)
{
    (|input| == 3 && input[1] == ' ') || 
    (|input| == 4 && input[1] == ' ' && input[3] == '\n')
}

predicate ValidHexDigit(c: char)
{
    c in {'A', 'B', 'C', 'D', 'E', 'F'}
}

predicate ValidInputFormat(input: string)
{
    |input| >= 3 &&
    ValidInput(input) &&
    ValidHexDigit(input[0]) &&
    ValidHexDigit(input[2])
}

predicate CorrectComparison(x: char, y: char, result: string)
{
    result in {"<\n", ">\n", "=\n"} &&
    ((x as int < y as int) <==> (result == "<\n")) &&
    ((x as int > y as int) <==> (result == ">\n")) &&
    ((x as int == y as int) <==> (result == "=\n"))
}

// <vc-helpers>
lemma HexDigitOrdering()
    ensures 'A' as int < 'B' as int < 'C' as int < 'D' as int < 'E' as int < 'F' as int
{
}

lemma ComparisonProperties(x: char, y: char)
    requires ValidHexDigit(x) && ValidHexDigit(y)
    ensures (x as int < y as int) || (x as int > y as int) || (x as int == y as int)
    ensures (x as int < y as int) ==> !(x as int > y as int) && !(x as int == y as int)
    ensures (x as int > y as int) ==> !(x as int < y as int) && !(x as int == y as int)
    ensures (x as int == y as int) ==> !(x as int < y as int) && !(x as int > y as int)
{
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires ValidInputFormat(stdin_input)
    ensures CorrectComparison(stdin_input[0], stdin_input[2], result)
// </vc-spec>
// <vc-code>
{
    var x := stdin_input[0];
    var y := stdin_input[2];
    
    if x as int < y as int {
        result := "<\n";
    } else if x as int > y as int {
        result := ">\n";
    } else {
        result := "=\n";
    }
}
// </vc-code>

