// <vc-preamble>
predicate IsDigitSpec(c: char) 
{
    (c as int) >= 48 && (c as int) <= 57
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IsInteger(text: array<char>) returns (result: bool)
    ensures result == (forall i :: 0 <= i < text.Length ==> IsDigitSpec(text[i]))
// </vc-spec>
// <vc-code>
{
  result := true;
  var i := 0;
  while i < text.Length
    invariant 0 <= i <= text.Length
    invariant result == (forall j :: 0 <= j < i ==> IsDigitSpec(text[j]))
  {
    if !IsDigitSpec(text[i]) {
      result := false;
      return;
    }
    i := i + 1;
  }
}
// </vc-code>
