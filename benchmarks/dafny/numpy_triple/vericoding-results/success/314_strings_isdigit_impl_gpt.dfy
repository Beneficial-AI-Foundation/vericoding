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
/* helper modified by LLM (iteration 3): trivial boolean wrapper for IsDigitString */
function IsDigitStringBool(s: string): bool
{
    IsDigitString(s)
}
// </vc-helpers>

// <vc-spec>
method IsDigit(a: seq<string>) returns (result: seq<bool>)
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |a| ==> result[i] == IsDigitString(a[i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): iterative construction with invariants to build the boolean sequence */
  var i := 0;
  var r: seq<bool> := [];
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |r| == i
    invariant forall j :: 0 <= j < i ==> r[j] == IsDigitString(a[j])
  {
    r := r + [IsDigitString(a[i])];
    i := i + 1;
  }
  result := r;
}
// </vc-code>
