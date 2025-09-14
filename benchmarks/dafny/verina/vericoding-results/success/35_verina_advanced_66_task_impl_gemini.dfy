// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function ReverseSeq<T>(s: seq<T>): seq<T> {
  if s == [] then []
  else ReverseSeq(s[1..]) + [s[0]]
}

function Join(parts: seq<string>, sep: char): string {
  if |parts| == 0 then ""
  else if |parts| == 1 then parts[0]
  else parts[0] + [sep] + Join(parts[1..], sep)
}
// </vc-helpers>

// <vc-spec>
method ReverseWords(words_str: string) returns (result: string)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): added loop invariants to prove slice safety */
{
    var words: seq<string> := [];
    var i := 0;
    while i < |words_str|
        invariant 0 <= i <= |words_str|
    {
        var word_start := i;
        while word_start < |words_str| && words_str[word_start] == ' '
            invariant i <= word_start <= |words_str|
        {
            word_start := word_start + 1;
        }

        if word_start < |words_str| {
            var word_end := word_start;
            while word_end < |words_str| && words_str[word_end] != ' '
                invariant word_start <= word_end <= |words_str|
            {
                word_end := word_end + 1;
            }
            words := words + [words_str[word_start..word_end]];
            i := word_end;
        } else {
            i := |words_str|;
        }
    }
    var reversed_words := ReverseSeq(words);
    result := Join(reversed_words, ' ');
}
// </vc-code>
