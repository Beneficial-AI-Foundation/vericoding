// <vc-preamble>
predicate IsDigit(c: char)
{
    '0' <= c <= '9'
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method CountDigits(s: string) returns (result: nat)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
  result := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant result >= 0
  {
    if IsDigit(s[i]) {
      result := result + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
