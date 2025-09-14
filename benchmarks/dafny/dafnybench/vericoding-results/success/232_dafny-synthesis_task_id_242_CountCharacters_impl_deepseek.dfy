

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method CountCharacters(s: string) returns (count: int)
    ensures count >= 0
    ensures count == |s|
// </vc-spec>
// <vc-code>
{
  count := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant count == i
  {
    count := count + 1;
    i := i + 1;
  }
}
// </vc-code>

