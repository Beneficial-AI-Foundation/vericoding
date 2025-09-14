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

// <vc-helpers>
lemma clean_input_removes_trailing_whitespace(s: string)
    ensures clean_input(clean_input(s)) == clean_input(s)
{
    if |s| == 0 {
    }
    else if s[|s|-1] == '\n' || s[|s|-1] == '\r' || s[|s|-1] == ' ' {
        clean_input_removes_trailing_whitespace(s[..|s|-1]);
        calc {
            clean_input(clean_input(s));
            clean_input(clean_input(s[..|s|-1]));
            { clean_input_removes_trailing_whitespace(s[..|s|-1]); }
            clean_input(s[..|s|-1]);
            clean_input(s);
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
requires |stdin_input| > 0
ensures result == "Yes\n" || result == "No\n"
ensures result == "Yes\n" <==> contains_digit_nine(clean_input(stdin_input))
ensures result == "No\n" <==> !contains_digit_nine(clean_input(stdin_input))
// </vc-spec>
// <vc-code>
{
    var cleaned := clean_input(stdin_input);
    if contains_digit_nine(cleaned) {
        result := "Yes\n";
    } else {
        result := "No\n";
    }
}
// </vc-code>

