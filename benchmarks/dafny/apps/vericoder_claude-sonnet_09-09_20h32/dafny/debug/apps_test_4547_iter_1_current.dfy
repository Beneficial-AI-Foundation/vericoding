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
lemma clean_input_preserves_digit_nine(s: string)
ensures contains_digit_nine(s) <==> contains_digit_nine(clean_input(s))
{
    if |s| == 0 {
        return;
    }
    if s[|s|-1] == '\n' || s[|s|-1] == '\r' || s[|s|-1] == ' ' {
        clean_input_preserves_digit_nine(s[..|s|-1]);
        assert contains_digit_nine(s[..|s|-1]) <==> contains_digit_nine(clean_input(s[..|s|-1]));
        assert clean_input(s) == clean_input(s[..|s|-1]);
        
        if contains_digit_nine(s) {
            var i :| 0 <= i < |s| && s[i] == '9';
            if i < |s| - 1 {
                assert s[i] == s[..|s|-1][i];
                assert contains_digit_nine(s[..|s|-1]);
            } else {
                assert s[i] == '9';
                assert s[|s|-1] == '9';
                assert s[|s|-1] != '\n' && s[|s|-1] != '\r' && s[|s|-1] != ' ';
                assert false;
            }
        }
        
        if contains_digit_nine(s[..|s|-1]) {
            var i :| 0 <= i < |s[..|s|-1]| && s[..|s|-1][i] == '9';
            assert 0 <= i < |s| && s[i] == '9';
            assert contains_digit_nine(s);
        }
    }
}

method contains_digit_nine_check(s: string) returns (found: bool)
ensures found <==> contains_digit_nine(s)
{
    found := false;
    var i := 0;
    while i < |s|
    invariant 0 <= i <= |s|
    invariant found <==> exists j :: 0 <= j < i && s[j] == '9'
    {
        if s[i] == '9' {
            found := true;
            return;
        }
        i := i + 1;
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
    var has_nine := contains_digit_nine_check(cleaned);
    clean_input_preserves_digit_nine(stdin_input);
    
    if has_nine {
        result := "Yes\n";
    } else {
        result := "No\n";
    }
}
// </vc-code>

