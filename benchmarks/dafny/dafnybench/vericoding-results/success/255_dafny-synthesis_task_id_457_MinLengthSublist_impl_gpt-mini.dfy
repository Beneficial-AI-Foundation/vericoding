

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method MinLengthSublist(s: seq<seq<int>>) returns (minSublist: seq<int>)
    requires |s| > 0
    ensures minSublist in s
    ensures forall sublist :: sublist in s ==> |minSublist| <= |sublist|
// </vc-spec>
// <vc-code>
{
  minSublist := s[0];
  var i := 1;
  while i < |s|
    invariant 1 <= i <= |s|
    invariant minSublist in s[..i]
    invariant forall k :: 0 <= k < i ==> |minSublist| <= |s[k]|
    decreases |s| - i
  {
    var cur := s[i];
    i := i + 1;
    if |cur| < |minSublist| {
      minSublist := cur;
    }
  }
}
// </vc-code>

