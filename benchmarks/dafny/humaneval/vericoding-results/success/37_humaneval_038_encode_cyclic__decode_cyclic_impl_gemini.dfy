// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method decode_cyclic(s: seq<int>) returns (res: seq<int>)

    ensures |s| == |res|
    ensures forall i :: |s| - |s| % 3 <= i < |s| ==> (res[i] == s[i])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 0 ==> res[i] == s[i + 2])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 1 ==> res[i] == s[i - 1])
// </vc-spec>
// <vc-code>
{
    var n := |s|;
    var arr := new int[n];
    var i := 0;
    var limit := n - n % 3;

    while i < limit
        invariant 0 <= i <= limit && i % 3 == 0
        invariant forall k :: 0 <= k < i && k % 3 == 0 ==> arr[k] == s[k+2]
        invariant forall k :: 0 <= k < i && k % 3 == 1 ==> arr[k] == s[k-1]
    {
        arr[i] := s[i+2];
        arr[i+1] := s[i];
        arr[i+2] := s[i+1];
        i := i + 3;
    }

    var j := limit;
    while j < n
        invariant limit <= j <= n
        invariant forall k :: 0 <= k < limit && k % 3 == 0 ==> arr[k] == s[k+2]
        invariant forall k :: 0 <= k < limit && k % 3 == 1 ==> arr[k] == s[k-1]
        invariant forall k :: limit <= k < j ==> arr[k] == s[k]
    {
        arr[j] := s[j];
        j := j + 1;
    }
    
    res := arr[..];
}
// </vc-code>
