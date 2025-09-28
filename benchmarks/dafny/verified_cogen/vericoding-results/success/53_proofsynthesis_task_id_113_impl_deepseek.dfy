// <vc-preamble>
predicate IsDigitSpec(c: char) 
{
    (c as int) >= 48 && (c as int) <= 57
}
// </vc-preamble>

// <vc-helpers>
predicate IsDigit(c: char) { (c as int) >= 48 && (c as int) <= 57 }
// </vc-helpers>

// <vc-spec>
method IsInteger(text: array<char>) returns (result: bool)
    ensures result == (forall i :: 0 <= i < text.Length ==> IsDigitSpec(text[i]))
// </vc-spec>
// <vc-code>
{
  var i := 0;
  result := true;
  while i < text.Length
    invariant 0 <= i <= text.Length
    invariant result == (forall j :: 0 <= j < i ==> IsDigit(text[j]))
  {
    if !IsDigit(text[i]) {
      result := false;
      return;
    }
    i := i + 1;
  }
}
// </vc-code>
