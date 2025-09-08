Given two hexadecimal digits X and Y (each being one of A, B, C, D, E, or F representing values 10, 11, 12, 13, 14, 15 respectively), 
compare their values and output the comparison result: "<" if X < Y, ">" if X > Y, "=" if X = Y.

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

method solve(stdin_input: string) returns (result: string)
    requires ValidInputFormat(stdin_input)
    ensures CorrectComparison(stdin_input[0], stdin_input[2], result)
{
    var x := stdin_input[0];
    var y := stdin_input[2];

    if x as int < y as int
    {
        result := "<\n";
    }
    else if x as int > y as int
    {
        result := ">\n";
    }
    else
    {
        result := "=\n";
    }
}
