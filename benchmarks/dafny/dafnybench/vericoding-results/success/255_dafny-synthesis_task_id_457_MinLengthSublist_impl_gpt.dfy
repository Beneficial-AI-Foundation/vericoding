

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
method MinLengthSublist(s: seq<seq<int>>) returns (minSublist: seq<int>)
    requires |s| > 0
    ensures minSublist in s
    ensures forall sublist :: sublist in s ==> |minSublist| <= |sublist|
// </vc-spec>
// <vc-code>
{
  var i := 1;
  minSublist := s[0];
  while i < |s|
    invariant 1 <= i <= |s|
    invariant exists j :: 0 <= j < i && minSublist == s[j]
    invariant forall k :: 0 <= k < i ==> |minSublist| <= |s[k]|
    decreases |s| - i
  {
    if |s[i]| < |minSublist| {
      minSublist := s[i];
    }
    i := i + 1;
  }
}
// </vc-code>

