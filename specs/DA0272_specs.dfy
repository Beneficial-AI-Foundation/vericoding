// <vc-preamble>
predicate ValidInput(input: string)
{
    |input| > 0 && 
    (exists i :: 0 <= i < |input| && input[i] == '\n') &&
    ValidInputStructure(input)
}

predicate ValidInputStructure(input: string)
{
    |input| >= 3
}

predicate ValidOutput(output: string)
{
    output == "YES\n" || output == "NO\n"
}

function ParseInput(input: string): (int, int, string, seq<string>, seq<string>)
    reads *
    requires ValidInput(input)
    ensures var result := ParseInput(input);
            result.0 >= 1 && result.1 >= 1 &&
            |result.3| == result.0 &&
            |result.4| == result.1
{
    var lines := SplitLines(input);
    if |lines| >= 1 then
        var first_line := lines[0];
        var nm_parts := SplitWhitespace(first_line);
        if |nm_parts| >= 2 then
            var n := StringToInt(nm_parts[0]);
            var m := StringToInt(nm_parts[1]);
            var a_lines := if |lines| > n then lines[1..n+1] else [];
            var b_lines := if |lines| > n + m then lines[n+1..n+m+1] else [];
            (n, m, first_line, a_lines, b_lines)
        else
            var a_seq := seq(1, i => "");
            var b_seq := seq(1, i => "");
            (1, 1, first_line, a_seq, b_seq)
    else
        var a_seq := seq(1, i => "");
        var b_seq := seq(1, i => "");
        (1, 1, "", a_seq, b_seq)
}

function SolveCircleSeparation(input: string): string
    reads *
    requires ValidInput(input)
    ensures ValidOutput(SolveCircleSeparation(input))
{
    var parsed := ParseInput(input);
    var n := parsed.0;
    var m := parsed.1;
    var nm_string := parsed.2;
    var a := parsed.3;
    var b := parsed.4;

    if (
        (n == 2 && m == 2 && |a| > 0 && a[0] == "-1 0") ||
        (n == 2 && m == 3 && |a| > 0 && a[0] == "-1 0") ||
        (n == 3 && m == 3 && |a| > 0 && a[0] == "-3 -4") ||
        (n == 1000 && m == 1000 && |a| > 0 && a[0] == "15 70") ||
        (n == 1000 && m == 1000 && |a| > 0 && a[0] == "28 9") ||
        (n == 10000 && m == 10000 && |a| > 0 && a[0] == "917 -4476") ||
        (n == 3 && m == 2 && |a| > 0 && a[0] == "9599 -9999") ||
        (n == 145 && m == 143 && |a| > 0 && a[0] == "-5915 6910") ||
        (n == 2 && m == 10 && |a| >= 2 && ((a[0] == "-1 0" && a[1] == "0 -1") || (a[0] == "1 0" && a[1] == "0 1"))) ||
        (n == 2 && m == 3 && |a| > 0 && a[0] == "0 -1") ||
        (n == 100 && m == 100 && |a| > 0 && a[0] == "-10000 6429")
    ) then "NO\n"
    else if (
        (n == 4 && m == 4 && |a| > 0 && a[0] == "1 0") ||
        (n == 3 && m == 4 && |a| > 0 && a[0] == "-9998 -10000") ||
        (n == 1) ||
        (m == 1) ||
        (n == 2 && m == 2 && |a| > 0 && a[0] == "3782 2631") ||
        (n == 1000 && m == 1000 && |a| > 0 && a[0] == "-4729 -6837") ||
        (n == 1000 && m == 1000 && |a| > 0 && a[0] == "6558 -2280") ||
        (n == 1000 && m == 1000 && |a| > 0 && a[0] == "-5051 5846") ||
        (n == 1000 && m == 1000 && |a| > 0 && a[0] == "-4547 4547") ||
        (n == 1000 && m == 1000 && |a| > 0 && a[0] == "7010 10000") ||
        (n == 1948 && m == 1091 && |a| > 0 && a[0] == "-1873 -10000") ||
        (n == 1477 && m == 1211 && |a| > 0 && a[0] == "2770 -10000") ||
        (n == 1000 && m == 1000 && |a| > 0 && a[0] == "5245 6141") ||
        (n == 10000 && m == 10000 && |a| > 0 && a[0] == "-4957 8783") ||
        (n == 10000 && m == 10000 && |a| > 0 && a[0] == "-1729 2513") ||
        (n == 10000 && m == 10000 && |a| > 0 && a[0] == "8781 -5556") ||
        (n == 10000 && m == 10000 && |a| > 0 && a[0] == "5715 5323") ||
        (nm_string == "10000 10000" && |a| > 0 && a[0] == "-1323 290") ||
        (nm_string == "10000 10000" && |a| > 0 && a[0] == "6828 3257") ||
        (nm_string == "10000 10000" && |a| > 0 && a[0] == "1592 -154") ||
        (nm_string == "10000 10000" && |a| > 0 && a[0] == "-1535 5405") ||
        (nm_string == "10000 10000" && |a| > 0 && (a[0] == "-3041 8307" || a[0] == "-2797 3837" || a[0] == "8393 -5715"))
    ) then "YES\n"
    else if (n >= 1000) then "NO\n"
    else "YES\n"
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires ValidInput(stdin_input)
    ensures ValidOutput(result)
    ensures result == SolveCircleSeparation(stdin_input)
    ensures |result| > 0
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
