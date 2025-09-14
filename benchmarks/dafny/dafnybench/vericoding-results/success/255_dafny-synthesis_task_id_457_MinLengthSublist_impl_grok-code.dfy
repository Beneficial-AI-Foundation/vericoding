

// <vc-helpers>
//
// </vc-helpers>

// <vc-spec>
method MinLengthSublist(s: seq<seq<int>>) returns (minSublist: seq<int>)
    requires |s| > 0
    ensures minSublist in s
    ensures forall sublist :: sublist in s ==> |minSublist| <= |sublist|
// </vc-spec>
// <vc-code>
{
  var minIndex := 0;
  if 1 < |s| {
    for i := 1 to |s|
      invariant 0 <= minIndex < |s|
      invariant forall k :: 0 <= k < i ==> |s[minIndex]| <= |s[k]|
    {
      if |s[i]| < |s[minIndex]| {
        minIndex := i;
      }
    }
  }
  minSublist := s[minIndex];
}
// </vc-code>

