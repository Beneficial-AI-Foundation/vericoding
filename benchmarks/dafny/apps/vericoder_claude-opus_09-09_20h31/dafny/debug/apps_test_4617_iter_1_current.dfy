predicate ValidInput(lines: seq<string>)
{
    |lines| >= 2 && |lines[0]| > 0 && |lines[1]| > 0
}

predicate IsSymmetric(first_row: string, second_row: string)
{
    reverse(first_row) == second_row
}

function split_lines(s: string): seq<string>
{
    if |s| == 0 then []
    else if s[0] == '\n' then [""] + split_lines(s[1..])
    else 
        var rest := split_lines(s[1..]);
        if |rest| == 0 then [[s[0]]]
        else [rest[0] + [s[0]]] + rest[1..]
}

function reverse(s: string): string
{
    if |s| == 0 then ""
    else reverse(s[1..]) + [s[0]]
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    ensures result == "YES\n" || result == "NO\n"
    ensures var normalized_input := stdin_input + if stdin_input[|stdin_input|-1] == '\n' then "" else "\n";
            var lines := split_lines(normalized_input);
            ValidInput(lines) ==> (result == "YES\n" <==> IsSymmetric(lines[0], lines[1]))
    ensures var normalized_input := stdin_input + if stdin_input[|stdin_input|-1] == '\n' then "" else "\n";
            var lines := split_lines(normalized_input);
            !ValidInput(lines) ==> result == "NO\n"
// </vc-spec>
// <vc-code>
{
    var normalized_input := stdin_input + if stdin_input[|stdin_input|-1] == '\n' then "" else "\n";
    var lines := split_lines(normalized_input);
    
    if ValidInput(lines) {
        if IsSymmetric(lines[0], lines[1]) {
            result := "YES\n";
        } else {
            result := "NO\n";
        }
    } else {
        result := "NO\n";
    }
}
// </vc-code>

