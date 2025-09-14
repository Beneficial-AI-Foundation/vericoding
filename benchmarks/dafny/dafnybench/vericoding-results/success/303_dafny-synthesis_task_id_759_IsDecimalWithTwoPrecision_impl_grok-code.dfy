

// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method IsDecimalWithTwoPrecision(s: string) returns (result: bool)
    ensures result ==> (exists i :: 0 <= i < |s| && s[i] == '.' && |s| - i - 1 == 2)
    ensures !result ==> !(exists i :: 0 <= i < |s| && s[i] == '.' && |s| - i - 1 == 2)
// </vc-spec>
// <vc-code>
{
  var found := false;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant found <==> exists k :: 0 <= k < i && s[k] == '.' && |s| - k - 1 == 2
  {
    if s[i] == '.' && |s| - i - 1 == 2 {
      found := true;
      i := |s|;  // cause loop to exit
    } else {
      i := i + 1;
    }
  }
  result := found;
}
// </vc-code>

