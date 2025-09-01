

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
// </vc-helpers>

// <vc-spec>
method count_upper(s: string) returns (cnt: int)
  // post-conditions-start
  ensures cnt == |set i | 0 <= i < |s| && i % 2 == 0 && is_upper_vowel(s[i])|
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  cnt := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant cnt == |set j | 0 <= j < i && j % 2 == 0 && is_upper_vowel(s[j])|
  {
    if i % 2 == 0 && is_upper_vowel(s[i]) {
      cnt := cnt + 1;
    }
    i := i + 1;
  }
}
// </vc-code>

function is_upper_vowel(c: char) : bool {
  c == 'A' || c == 'E' || c == 'U' || c == 'I' || c == 'O'
}
// pure-end