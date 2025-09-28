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
/* code modified by LLM (iteration 3): Added invariant |unique| <= i to prove count <= |s| */
{
  var unique: set<char> := {};
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant unique == set k | 0 <= k < i :: to_lower_char(s[k])
    invariant |unique| <= i
  {
    unique := unique + {to_lower_char(s[i])};
    i := i + 1;
  }
  count := |unique|;
}
// </vc-code>
