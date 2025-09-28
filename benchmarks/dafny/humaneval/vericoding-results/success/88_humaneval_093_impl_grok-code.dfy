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
function encodeChar(c: char): char
    requires ('a' <= c <= 'z') || ('A' <= c <= 'Z') || c == ' '
{
    if c == ' ' then ' '
    else if isVowel(c) then swapCase(getVowelReplacement(c))
    else swapCase(c)
}
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
  var msg := message;
  var result_chars: seq<char> := [];
  for i := 0 to |msg|
    invariant 0 <= i <= |msg|
    invariant |result_chars| == i
    invariant forall k :: 0 <= k < i ==> result_chars[k] == encodeChar(msg[k])
  {
    result_chars := result_chars + [encodeChar(msg[i])];
  }
  result := result_chars;
}
// </vc-code>
