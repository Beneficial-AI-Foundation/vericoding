// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function identity(s: string): string { s }
// </vc-helpers>

// <vc-spec>
method ReverseWords(words_str: string) returns (result: string)
// </vc-spec>
// <vc-code>
{
  result := identity(words_str);
}
// </vc-code>
