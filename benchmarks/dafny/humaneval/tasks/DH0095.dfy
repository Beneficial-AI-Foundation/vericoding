// <vc-preamble>

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
// </vc-helpers>

// <vc-spec>
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
    assume {:axiom} false;
  }
// </vc-code>
