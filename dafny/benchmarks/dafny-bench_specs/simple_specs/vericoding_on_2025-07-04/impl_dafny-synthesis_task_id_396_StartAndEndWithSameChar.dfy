//IMPL
method StartAndEndWithSameChar(s: string) returns (result: bool)
  requires |s| > 0
  ensures result <==> s[0] == s[|s| - 1]
{
  /* code modified by LLM (iteration 1): direct assignment should satisfy postcondition */
  result := s[0] == s[|s| - 1];
}