

// <vc-helpers>
function count_upper_helper(s: string, index: int, cnt: int): (result: int)
  requires 0 <= index <= |s|
  ensures result == cnt + |set i | index <= i < |s| && i % 2 == 0 && is_upper_vowel(s[i])|
  decreases |s| - index
{
  if index >= |s| then
    cnt
  else if index % 2 == 0 && is_upper_vowel(s[index]) then
    count_upper_helper(s, index + 1, cnt + 1)
  else
    count_upper_helper(s, index + 1, cnt)
}

lemma {:induction false} CountUpperHelperLemma(s: string, index: int, cnt: int)
  requires 0 <= index <= |s|
  ensures count_upper_helper(s, index, cnt) == cnt + |set i | index <= i < |s| && i % 2 == 0 && is_upper_vowel(s[i])|
  decreases |s| - index
{
  if index < |s| {
    if index % 2 == 0 && is_upper_vowel(s[index]) {
      CountUpperHelperLemma(s, index + 1, cnt + 1);
    } else {
      CountUpperHelperLemma(s, index + 1, cnt);
    }
  }
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method count_upper(s: string) returns (cnt: int)
  // post-conditions-start
  ensures cnt == |set i | 0 <= i < |s| && i % 2 == 0 && is_upper_vowel(s[i])|
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  CountUpperHelperLemma(s, 0, 0);
  cnt := count_upper_helper(s, 0, 0);
}
// </vc-code>

function is_upper_vowel(c: char) : bool {
  c == 'A' || c == 'E' || c == 'U' || c == 'I' || c == 'O'
}
// pure-end