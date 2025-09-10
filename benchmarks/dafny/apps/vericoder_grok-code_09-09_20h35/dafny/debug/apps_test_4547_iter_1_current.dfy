function clean_input(s: string): string
{
    if |s| == 0 then s
    else if s[|s|-1] == '\n' || s[|s|-1] == '\r' || s[|s|-1] == ' ' then
        clean_input(s[..|s|-1])
    else s
}

predicate contains_digit_nine(s: string)
{
    exists i :: 0 <= i < |s| && s[i] == '9'
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
requires |stdin_input| > 0
ensures result == "Yes\n" || result == "No\n"
ensures result == "Yes\n" <==> contains_digit_nine(clean_input(stdin_input))
ensures result == "No\n" <==> !contains_digit_nine(clean_input(stdin_input))
// </vc-spec>
// <vc-code>
{
  var cleaned := clean_input(stdin_input);
  var found := false;
  for i := 0 to |cleaned| 
    invariant 0 <= i <= |cleaned|
    invariant found <==> exists k :: 0 <= k < i && cleaned[k] == '9'
  {
    if cleaned[i] == '9' {
      found := true;
      break;
    }
  }
  if found {
    result := "Yes\n";
  } else {
    result := "No\n";
  }
}
// </vc-code>

