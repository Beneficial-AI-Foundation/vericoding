// <vc-preamble>

function to_lower_char(c: char): char
{
    if 'A' <= c <= 'Z' then
        (c as int - 'A' as int + 'a' as int) as char
    else
        c
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method count_distinct_characters(s: string) returns (count: int)
    ensures count >= 0
    ensures count <= |s|
    ensures count == |set i | 0 <= i < |s| :: to_lower_char(s[i])|
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): implemented loop to compute distinct characters with invariant */
{
  var chars: set<char> := {};
  var i: int := 0;
  while i < |s|
      invariant 0 <= i <= |s|
      invariant chars == set j | 0 <= j < i :: to_lower_char(s[j])
      invariant |chars| <= i
  {
      chars := chars + {to_lower_char(s[i])};
      i := i + 1;
  }
  count := |chars|;
}
// </vc-code>
