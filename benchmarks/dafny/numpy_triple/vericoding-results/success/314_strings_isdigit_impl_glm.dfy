// <vc-preamble>
// Predicate to check if a character is a digit (0-9)
predicate IsDigitChar(c: char)
{
    '0' <= c <= '9'
}

// Predicate to check if all characters in a string are digits
predicate AllDigits(s: string)
{
    forall i :: 0 <= i < |s| ==> IsDigitChar(s[i])
}

// Predicate to check if a string satisfies the isdigit condition:
// non-empty and all characters are digits
predicate IsDigitString(s: string)
{
    |s| > 0 && AllDigits(s)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IsDigit(a: seq<string>) returns (result: seq<bool>)
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |a| ==> result[i] == IsDigitString(a[i])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed loop bounds and added invariant to prove postcondition */
{
  var arr := new bool[|a|];
  for i := 0 to |a|
    invariant 0 <= i <= |a|
    invariant forall j :: 0 <= j < i ==> arr[j] == IsDigitString(a[j])
  {
    arr[i] := IsDigitString(a[i]);
  }
  result := arr[..];
}
// </vc-code>
