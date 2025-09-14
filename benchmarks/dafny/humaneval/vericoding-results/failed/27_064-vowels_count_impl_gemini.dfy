// <vc-preamble>
function is_vowel(c: char): bool
  ensures is_vowel(c) <==> c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
{
  c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
}
// </vc-preamble>

// <vc-helpers>
function NumVowels(s: string): nat { |(set i | 0 <= i < |s| && is_vowel(s[i]))| }

/* helper modified by LLM (iteration 2): added lemma to relate vowel count of a string and its prefix */
lemma NumVowelsAppend(s: string, c: char)
  ensures NumVowels(s + [c]) == NumVowels(s) + (if is_vowel(c) then 1 else 0)
{
}
// </vc-helpers>

// <vc-spec>
method vowel_count(s: string) returns (count: int)

  ensures count >= 0
  ensures count == |(set i | 0 <= i < |s| && is_vowel(s[i]))| + if |s| > 0 && s[|s| - 1] == 'y' then 1 else 0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): added explicit lemma call to prove loop invariant */
  count := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant count == NumVowels(s[..i])
  {
    if is_vowel(s[i]) {
      count := count + 1;
    }
    NumVowelsAppend(s[..i], s[i]);
    i := i + 1;
  }

  if |s| > 0 && s[|s| - 1] == 'y' {
    count := count + 1;
  }
}
// </vc-code>
