predicate ValidInput(n: int)
{
  n >= 1
}

predicate ValidOutput(s: string, n: int)
{
  |s| == n &&
  (forall i :: 0 <= i < |s| ==> s[i] == 'a' || s[i] == 'b' || s[i] == 'c') &&
  (forall i :: 0 <= i <= |s| - 3 ==> !(s[i] == s[i+2]))
}

predicate MinimalCUsage(s: string)
{
  forall i :: 0 <= i < |s| ==> s[i] == 'a' || s[i] == 'b'
}

// <vc-helpers>
function GenerateString(n: int) : string
  requires n >= 1
  ensures |GenerateString(n)| == n
  ensures forall i :: 0 <= i < |GenerateString(n)| ==> GenerateString(n)[i] == 'a' || GenerateString(n)[i] == 'b'
  ensures forall i :: 0 <= i <= |GenerateString(n)| - 3 ==> !(GenerateString(n)[i] == GenerateString(n)[i+2])
{
  if n == 1 then "a"
  else if n == 2 then "ab"
  else
    var prev := GenerateString(n-2);
    var new_char := 'a';
    if prev[|prev|-1] == 'a' then new_char := 'b';
    else new_char := 'a'; // This line was missing an 'else' branch
    return prev + new_char
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: string)
  requires ValidInput(n)
  ensures ValidOutput(result, n)
  ensures MinimalCUsage(result)
// </vc-spec>
// <vc-code>
{
  return GenerateString(n);
}
// </vc-code>

