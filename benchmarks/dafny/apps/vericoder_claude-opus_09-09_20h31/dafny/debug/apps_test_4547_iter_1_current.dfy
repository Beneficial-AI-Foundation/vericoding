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
lemma CleanInputIdempotent(s: string)
    ensures clean_input(clean_input(s)) == clean_input(s)
{
    var cleaned := clean_input(s);
    if |cleaned| == 0 {
        // empty string case
    } else if cleaned[|cleaned|-1] == '\n' || cleaned[|cleaned|-1] == '\r' || cleaned[|cleaned|-1] == ' ' {
        // This case cannot happen by definition of clean_input
        assert false;
    } else {
        // cleaned is already clean
    }
}

lemma ContainsDigitNineInPrefix(s: string, i: nat)
    requires i < |s| && s[i] == '9'
    ensures contains_digit_nine(s)
{
    // Witness that digit '9' exists at position i
}

lemma NoDigitNineInEmptyString()
    ensures !contains_digit_nine("")
{
    // Empty string cannot contain '9'
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
    var i := 0;
    var found := false;
    
    while i < |cleaned|
        invariant 0 <= i <= |cleaned|
        invariant found ==> exists j :: 0 <= j < i && cleaned[j] == '9'
        invariant !found ==> forall j :: 0 <= j < i ==> cleaned[j] != '9'
        invariant found ==> contains_digit_nine(cleaned)
    {
        if cleaned[i] == '9' {
            found := true;
            ContainsDigitNineInPrefix(cleaned, i);
        }
        i := i + 1;
    }
    
    if found {
        result := "Yes\n";
    } else {
        result := "No\n";
    }
}
// </vc-code>

