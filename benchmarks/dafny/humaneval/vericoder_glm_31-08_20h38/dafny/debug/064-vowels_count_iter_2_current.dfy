

// <vc-helpers>
ghost function count_vowels_in_first_i(s: string, i: int): int
    requires 0 <= i <= |s|
    ensures count_vowels_in_first_i(s, i) == |set j | 0 <= j < i && is_vowel(s[j])|
{
    if i == 0 then 0
    else count_vowels_in_first_i(s, i-1) + (if is_vowel(s[i-1]) then 1 else 0)
}
// </vc-helpers>

// <vc-spec>
method vowel_count(s: string) returns (count: int)
  // post-conditions-start
  ensures count >= 0
  ensures count == |(set i | 0 <= i < |s| && is_vowel(s[i]))| + if |s| > 0 && s[|s| - 1] == 'y' then 1 else 0
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
    var c := 0;
    for i := 0 to |s|
        invariant 0 <= i <= |s|
        invariant c == count_vowels_in_first_i(s, i)
    {
        if (is_vowel(s[i])) then
            c := c + 1;
    }
    if |s| > 0 && s[|s|-1] == 'y' then
        c := c + 1;
    count := c;
}
// </vc-code>

function is_vowel(c: char): bool
  ensures is_vowel(c) <==> c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
{
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
}
// pure-end