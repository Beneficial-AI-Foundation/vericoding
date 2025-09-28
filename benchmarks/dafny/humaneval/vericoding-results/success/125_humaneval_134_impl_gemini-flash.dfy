// <vc-preamble>

predicate IsAlpha(c: char)
{
    ('a' <= c <= 'z') || ('A' <= c <= 'Z')
}

predicate ValidLastCharIsStandaloneLetter(txt: string)
{
    |txt| > 0 && IsAlpha(txt[|txt| - 1]) && (|txt| == 1 || txt[|txt| - 2] == ' ')
}
// </vc-preamble>

// <vc-helpers>
predicate IsSpace(c: char)
{
    c == ' '
}
// </vc-helpers>

// <vc-spec>
method check_if_last_char_is_a_letter(txt: string) returns (result: bool)
    ensures result == ValidLastCharIsStandaloneLetter(txt)
// </vc-spec>
// <vc-code>
{
    if |txt| == 0 {
        result := false;
    } else {
        var lastChar := txt[|txt| - 1];
        if !IsAlpha(lastChar) {
            result := false;
        } else {
            if |txt| == 1 {
                result := true;
            } else {
                var secondLastChar := txt[|txt| - 2];
                result := IsSpace(secondLastChar);
            }
        }
    }
}
// </vc-code>
