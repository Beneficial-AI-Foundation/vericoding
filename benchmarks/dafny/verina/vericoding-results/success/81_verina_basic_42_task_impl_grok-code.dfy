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
var count := 0;
for i := 0 to |s|
{
  if IsDigit(s[i])
  {
    count := count + 1;
  }
}
result := count;
}
// </vc-code>
