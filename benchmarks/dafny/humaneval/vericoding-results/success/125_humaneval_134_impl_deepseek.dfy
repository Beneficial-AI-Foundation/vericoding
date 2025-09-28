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

function ValidLastCharIsStandaloneLetterHelper(txt: string): bool
{
    if |txt| == 0 then false
    else if |txt| == 1 then IsAlpha(txt[0])
    else IsAlpha(txt[|txt| - 1]) && txt[|txt| - 2] == ' '
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
    } else if |txt| == 1 {
        result := IsAlpha(txt[0]);
    } else {
        result := IsAlpha(txt[|txt| - 1]) && txt[|txt| - 2] == ' ';
    }
}
// </vc-code>
