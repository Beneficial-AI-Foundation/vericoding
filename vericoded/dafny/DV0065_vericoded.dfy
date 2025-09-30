// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function ReverseWordList(words: seq<string>): seq<string>
{
  if |words| == 0 then []
  else ReverseWordList(words[1..]) + [words[0]]
}

function Split(s: string, delimiter: char): seq<string>
  decreases |s|
{
  if |s| == 0 then
    []
  else
    var idx := FindDelimiter(s, delimiter, 0);
    if idx == |s| then
      [s]
    else
      [s[..idx]] + Split(s[idx+1..], delimiter)
}

function FindDelimiter(s: string, delimiter: char, start: nat): nat
  requires start <= |s|
  ensures FindDelimiter(s, delimiter, start) <= |s|
  decreases |s| - start
{
  if start >= |s| then
    |s|
  else if s[start] == delimiter then
    start
  else
    FindDelimiter(s, delimiter, start + 1)
}

function Join(words: seq<string>, delimiter: string): string
{
  if |words| == 0 then
    ""
  else if |words| == 1 then
    words[0]
  else
    words[0] + delimiter + Join(words[1..], delimiter)
}
// </vc-helpers>

// <vc-spec>
method ReverseWords(words_str: string) returns (result: string)
// </vc-spec>
// <vc-code>
{
  var words := Split(words_str, ' ');
  var reversed := ReverseWordList(words);
  result := Join(reversed, " ");
}
// </vc-code>
