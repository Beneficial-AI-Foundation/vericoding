

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
        invariant minSublist in s[0..i]
        invariant forall j :: 0 <= j < i ==> |minSublist| <= |s[j]|
    {
        if |s[i]| < |minSublist| {
            minSublist := s[i];
        }
        i := i + 1;
    }
}
// </vc-code>

