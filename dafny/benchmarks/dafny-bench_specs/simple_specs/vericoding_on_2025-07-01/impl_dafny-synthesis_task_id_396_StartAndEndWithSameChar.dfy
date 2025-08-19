The method signature shows:
- Input: a non-empty string `s` (guaranteed by the precondition `|s| > 0`)
- Output: a boolean `result`
- Postcondition: `result` should be true if and only if the first character equals the last character

The implementation is straightforward - I need to compare `s[0]` (first character) with `s[|s| - 1]` (last character).

//IMPL
method StartAndEndWithSameChar(s: string) returns (result: bool)
  requires |s| > 0
  ensures result <==> s[0] == s[|s| - 1]
{
  result := s[0] == s[|s| - 1];
}