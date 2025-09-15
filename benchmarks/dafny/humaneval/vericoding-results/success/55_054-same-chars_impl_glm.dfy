// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function string_to_char_set(s: string): set<char> { set i | i in s }
// </vc-helpers>

// <vc-spec>
method same_chars(s0 : string, s1 : string) returns (b : bool)

    ensures b == ((set i | i in s0) == (set i | i in s1))
// </vc-spec>
// <vc-code>
{
  b := (string_to_char_set(s0) == string_to_char_set(s1));
}
// </vc-code>
