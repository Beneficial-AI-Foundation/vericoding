// <vc-preamble>
// ======= TASK =======
// Determine if the last character of a string is an alphabetical character that stands alone
// (not part of a word). A "word" is defined as a group of characters separated by spaces.
// Return True if the last character is a letter AND is not part of a word, False otherwise.
// A standalone letter is either the entire string (single character) or a letter preceded by a space.

// ======= SPEC REQUIREMENTS =======
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
// ======= HELPERS =======
// </vc-helpers>

// <vc-spec>
// ======= MAIN METHOD =======
method check_if_last_char_is_a_letter(txt: string) returns (result: bool)
    ensures result == ValidLastCharIsStandaloneLetter(txt)
// </vc-spec>
// <vc-code>
{
    // Check if string is empty
    if |txt| == 0 {
        return false;
    }

    // Get the last character
    var lastChar := txt[|txt| - 1];

    // Check if last character is alphabetical
    if !IsAlpha(lastChar) {
        return false;
    }

    // If string has only one character, it's not part of a word
    if |txt| == 1 {
        return true;
    }

    // Check if the character before the last one is a space
    // This ensures the last character is not part of a word
    return txt[|txt| - 2] == ' ';
}
// </vc-code>
