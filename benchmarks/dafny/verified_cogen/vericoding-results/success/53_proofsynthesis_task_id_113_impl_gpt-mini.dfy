// <vc-preamble>
predicate IsDigitSpec(c: char) 
{
    (c as int) >= 48 && (c as int) <= 57
}
// </vc-preamble>

// <vc-helpers>
function AllDigits(s: seq<char>): bool { forall i :: 0 <= i < |s| ==> IsDigitSpec(s[i]) }
// </vc-helpers>

// <vc-spec>
method IsInteger(text: array<char>) returns (result: bool)
    ensures result == (forall i :: 0 <= i < text.Length ==> IsDigitSpec(text[i]))
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var all := true;
  while i < text.Length
    invariant 0 <= i <= text.Length
    invariant all == (forall j :: 0 <= j < i ==> IsDigitSpec(text[j]))
  {
    all := all && IsDigitSpec(text[i]);
    i := i + 1;
  }
  result := all;
}
// </vc-code>
