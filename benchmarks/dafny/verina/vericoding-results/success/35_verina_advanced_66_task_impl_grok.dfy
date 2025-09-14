// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added decreases clause */
function ReverseString(s: string): string
  decreases |s|
{
  if |s| == 0 then "" else ReverseString(s[1..]) + [s[0]]
}
// </vc-helpers>

// <vc-spec>
method ReverseWords(words_str: string) returns (result: string)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): added loop invariants to prove slice bounds */
  var full_reverse := ReverseString(words_str);
  var res: string := "";
  var i: int := 0;
  while i < |full_reverse|
    invariant 0 <= i <= |full_reverse|
    decreases |full_reverse| - i
  {
    if full_reverse[i] == ' ' {
      res := res + " ";
      i := i + 1;
    } else {
      var j := i;
      while j < |full_reverse| && full_reverse[j] != ' '
        invariant i <= j <= |full_reverse|
        decreases |full_reverse| - j
      {
        j := j + 1;
      }
      var word := full_reverse[i..j];
      var rev_word := ReverseString(word);
      res := res + rev_word;
      i := j;
    }
  }
  result := res;
}
// </vc-code>
