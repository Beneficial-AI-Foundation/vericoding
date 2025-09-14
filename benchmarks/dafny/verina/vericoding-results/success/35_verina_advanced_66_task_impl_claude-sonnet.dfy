// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): fixed sequence slicing bounds error */
function SplitBySpaces(s: string): seq<string>
    decreases |s|
{
    if |s| == 0 then []
    else
        var firstSpace := FindFirstSpace(s, 0);
        if firstSpace == -1 then [s]
        else if firstSpace >= 0 && firstSpace < |s| && firstSpace + 1 <= |s| then
            var word := s[0..firstSpace];
            var rest := s[firstSpace+1..];
            [word] + SplitBySpaces(rest)
        else [s]
}

function FindFirstSpace(s: string, start: int): int
    requires 0 <= start <= |s|
    decreases |s| - start
{
    if start >= |s| then -1
    else if s[start] == ' ' then start
    else FindFirstSpace(s, start + 1)
}

function ReverseSequence<T>(s: seq<T>): seq<T>
    decreases |s|
{
    if |s| == 0 then []
    else ReverseSequence(s[1..]) + [s[0]]
}

function JoinWithSpaces(words: seq<string>): string
    decreases |words|
{
    if |words| == 0 then ""
    else if |words| == 1 then words[0]
    else words[0] + " " + JoinWithSpaces(words[1..])
}
// </vc-helpers>

// <vc-spec>
method ReverseWords(words_str: string) returns (result: string)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): using fixed helper functions */
    var words := SplitBySpaces(words_str);
    var reversed := ReverseSequence(words);
    result := JoinWithSpaces(reversed);
}
// </vc-code>
