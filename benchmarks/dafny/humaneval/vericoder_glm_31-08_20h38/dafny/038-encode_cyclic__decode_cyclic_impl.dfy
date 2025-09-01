method encode_cyclic(s: seq<int>) returns (res: seq<int>) 
    // post-conditions-start
    ensures |s| == |res|
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 0 ==> res[i] == s[i + 1])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 1 ==> res[i] == s[i + 1])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 2 ==> res[i] == s[i - 2])
    ensures forall i :: |s| - |s| % 3 <= i < |s| ==> (res[i] == s[i])
    // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
// (empty)
// </vc-helpers>

// <vc-spec>
method decode_cyclic(s: seq<int>) returns (res: seq<int>)
    // post-conditions-start
    ensures |s| == |res|
    ensures forall i :: |s| - |s| % 3 <= i < |s| ==> (res[i] == s[i])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 0 ==> res[i] == s[i + 2])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 1 ==> res[i] == s[i - 1])
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
        var n := |s|;
        var arr := new int[n];
        // Handle incomplete group at the end
        for i := n - n % 3 to n
            invariant n - n%3 <= i <= n
            invariant forall k :: n - n%3 <= k < i ==> arr[k] == s[k]
        {
            arr[i] := s[i];
        }
        // Process complete groups of three
        var groupCount := n / 3;
        for j := 0 to groupCount
            invariant 0 <= j <= groupCount
            invariant forall k :: n - n%3 <= k < n ==> arr[k] == s[k]
            invariant forall k :: 0 <= k < j*3 ==>
                (k % 3 == 0 ==> arr[k] == s[k+2]) &&
                (k % 3 == 1 ==> arr[k] == s[k-1])
        {
            var i := j * 3;
            arr[i] := s[i+2];
            arr[i+1] := s[i];
            arr[i+2] := s[i+1];
        }
        return arr[..];
}
// </vc-code>

