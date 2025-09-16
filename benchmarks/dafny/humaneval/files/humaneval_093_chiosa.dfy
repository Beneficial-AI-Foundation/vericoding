// <vc-preamble>
// ======= TASK =======
// Encode a message by applying two transformations to each character:
// 1. Replace vowels (a, e, i, o, u) with the letter that appears 2 positions later in the alphabet
// 2. Swap the case of all letters (uppercase ↔ lowercase)
// Apply both transformations: first replace vowels, then swap case of the result.
// Spaces are preserved unchanged. Assume input contains only letters and spaces.

// ======= SPEC REQUIREMENTS =======
predicate isVowel(c: char)
{
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' ||
    c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
}

function getVowelReplacement(c: char): char
    requires isVowel(c)
{
    match c
        case 'a' => 'c'
        case 'e' => 'g' 
        case 'i' => 'k'
        case 'o' => 'q'
        case 'u' => 'w'
        case 'A' => 'C'
        case 'E' => 'G'
        case 'I' => 'K'
        case 'O' => 'Q'
        case 'U' => 'W'
}

function swapCase(c: char): char
{
    if 'a' <= c <= 'z' then
        (c as int - 'a' as int + 'A' as int) as char
    else if 'A' <= c <= 'Z' then
        (c as int - 'A' as int + 'a' as int) as char
    else
        c
}
// </vc-preamble>

// <vc-helpers>
// ======= HELPERS =======
// </vc-helpers>

// <vc-spec>
// ======= MAIN METHOD =======
method encode(message: string) returns (result: string)
    requires forall i :: 0 <= i < |message| ==> (('a' <= message[i] <= 'z') || ('A' <= message[i] <= 'Z') || message[i] == ' ')
    ensures |result| == |message|
    ensures forall i :: 0 <= i < |message| ==> 
        if message[i] == ' ' then result[i] == ' '
        else if isVowel(message[i]) then result[i] == swapCase(getVowelReplacement(message[i]))
        else result[i] == swapCase(message[i])
// </vc-spec>
// <vc-code>
{
    result := "";
    var i := 0;

    while i < |message|
        invariant 0 <= i <= |message|
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==> 
            if message[j] == ' ' then result[j] == ' '
            else if isVowel(message[j]) then result[j] == swapCase(getVowelReplacement(message[j]))
            else result[j] == swapCase(message[j])
    {
        var c := message[i];
        if c == ' ' {
            result := result + [' '];
        } else if isVowel(c) {
            var replacement := getVowelReplacement(c);
            var swapped := swapCase(replacement);
            result := result + [swapped];
        } else {
            var swapped := swapCase(c);
            result := result + [swapped];
        }
        i := i + 1;
    }
}
// </vc-code>
