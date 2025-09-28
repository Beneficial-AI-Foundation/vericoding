// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function ReverseSeq<T>(s: seq<T>): seq<T>
{
  if |s| == 0 then []
  else [s[|s|-1]] + ReverseSeq(s[0..|s|-1])
}

function JoinWords(words: seq<string>): string
{
  if |words| == 0 then ""
  else if |words| == 1 then words[0]
       else words[0] + " " + JoinWords(words[1..])
}

function SplitWords(s: string, current: string, words: seq<string>): seq<string>
{
  if |s| == 0 then if |current| > 0 then words + [current] else words
  else if s[0] == ' ' then SplitWords(s[1..], "", if |current| > 0 then words + [current] else words)
       else SplitWords(s[1..], current + [s[0]], words)
}

/* helper modified by LLM (iteration 4): fixed compilation error by removing var declaration and simplifying ReverseWordsHelper to direct expression */
function ReverseWordsHelper(s: string): string
{
  JoinWords(ReverseSeq(SplitWords(s, "", [])))
}
// </vc-helpers>

// <vc-spec>
method ReverseWords(words_str: string) returns (result: string)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): kept the call to ReverseWordsHelper since helper is fixed */
{
  result := ReverseWordsHelper(words_str);
}
// </vc-code>
