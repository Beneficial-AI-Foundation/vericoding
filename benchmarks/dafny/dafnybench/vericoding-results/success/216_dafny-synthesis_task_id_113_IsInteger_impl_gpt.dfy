predicate IsDigit(c: char)
{
    48 <= c as int <= 57
}

// <vc-helpers>
// <vc-helpers>

// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method IsInteger(s: string) returns (result: bool)
    ensures result <==> (|s| > 0) && (forall i :: 0 <= i < |s| ==> IsDigit(s[i]))
// </vc-spec>
// <vc-code>
{
  var ok := true;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant ok <==> (forall j :: 0 <= j < i ==> IsDigit(s[j]))
    decreases |s| - i
  {
    ok := ok && IsDigit(s[i]);
    i := i + 1;
  }
  result := (|s| > 0) && ok;
}
// </vc-code>

