

// <vc-helpers>
lemma MinLengthExists(s: seq<seq<int>>)
    requires |s| > 0
    ensures exists minSublist :: minSublist in s && (forall sublist :: sublist in s ==> |minSublist| <= |sublist|)
{
    var index := 0;
    var minIndex := 0;
    var minLength := |s[0]|;
    
    while index < |s|
        invariant 0 <= index <= |s|
        invariant minIndex < |s|
        invariant minLength == |s[minIndex]|
        invariant forall j :: 0 <= j < index ==> minLength <= |s[j]|
    {
        if |s[index]| < minLength {
            minLength := |s[index]|;
            minIndex := index;
        }
        index := index + 1;
    }
    
    assert s[minIndex] in s;
    assert forall sublist :: sublist in s ==> |s[minIndex]| <= |sublist|;
}
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
    var minLength := |s[0]|;
    var i := 1;
    
    while i < |s|
        invariant 1 <= i <= |s|
        invariant 0 <= minIndex < |s|
        invariant minLength == |s[minIndex]|
        invariant forall j :: 0 <= j < i ==> minLength <= |s[j]|
    {
        if |s[i]| < minLength {
            minLength := |s[i]|;
            minIndex := i;
        }
        i := i + 1;
    }
    
    minSublist := s[minIndex];
}
// </vc-code>

