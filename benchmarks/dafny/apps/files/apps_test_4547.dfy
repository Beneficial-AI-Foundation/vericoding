Given a two-digit integer N (10 ≤ N ≤ 99), determine whether the digit 9 appears 
in the decimal representation of N. Return "Yes" if 9 appears, "No" otherwise.

function clean_input(s: string): string
{
    if |s| == 0 then s
    else if s[|s|-1] == '\n' || s[|s|-1] == '\r' || s[|s|-1] == ' ' then
        clean_input(s[..|s|-1])
    else s
}

predicate contains_digit_nine(s: string)
{
    exists i :: 0 <= i < |s| && s[i] == '9'
}

method solve(stdin_input: string) returns (result: string)
requires |stdin_input| > 0
ensures result == "Yes\n" || result == "No\n"
ensures result == "Yes\n" <==> contains_digit_nine(clean_input(stdin_input))
ensures result == "No\n" <==> !contains_digit_nine(clean_input(stdin_input))
{
    var n := stdin_input;

    // Remove trailing whitespace/newline if present
    while |n| > 0 && (n[|n|-1] == '\n' || n[|n|-1] == '\r' || n[|n|-1] == ' ')
    invariant clean_input(n) == clean_input(stdin_input)
    invariant |n| <= |stdin_input|
    {
        n := n[..|n|-1];
    }

    assert n == clean_input(stdin_input);

    // Check if '9' is present in the string
    var contains_nine := false;
    var i := 0;
    while i < |n|
    invariant 0 <= i <= |n|
    invariant contains_nine <==> exists j :: 0 <= j < i && n[j] == '9'
    {
        if n[i] == '9' {
            contains_nine := true;
            break;
        }
        i := i + 1;
    }

    assert contains_nine <==> exists j :: 0 <= j < |n| && n[j] == '9';
    assert n == clean_input(stdin_input);
    assert contains_nine <==> contains_digit_nine(clean_input(stdin_input));

    if contains_nine {
        result := "Yes\n";
    } else {
        result := "No\n";
    }
}
