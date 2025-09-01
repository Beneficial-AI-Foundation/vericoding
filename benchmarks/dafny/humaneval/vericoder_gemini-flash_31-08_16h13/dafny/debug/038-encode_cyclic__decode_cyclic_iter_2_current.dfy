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
    res := new int[n];

    var i := 0;
    while i < n - n % 3
        invariant 0 <= i <= n - n % 3
        invariant |res| == n
        invariant forall k :: 0 <= k < i && k % 3 == 0 ==> res[k] == s[k + 2]
        invariant forall k :: 0 <= k < i && k % 3 == 1 ==> res[k] == s[k - 1]
        invariant forall k :: 0 <= k < i && k % 3 == 2 ==> res[k] == s[k]
    {
        if i % 3 == 0 {
            res[i] := s[i + 2];
        } else if i % 3 == 1 {
            res[i] := s[i - 1];
        } else { // i % 3 == 2
            res[i] := s[i]; // This part of the sequence is stable
        }
        i := i + 1;
    }

    while i < n
        invariant n - n % 3 <= i <= n
        invariant |res| == n
        invariant forall k :: n - n % 3 <= k < i ==> res[k] == s[k]
        invariant forall k :: 0 <= k < n - n % 3 && k % 3 == 0 ==> res[k] == s[k + 2]
        invariant forall k :: 0 <= k < n - n % 3 && k % 3 == 1 ==> res[k] == s[k - 1]
        invariant forall k :: 0 <= k < n - n % 3 && k % 3 == 2 ==> res[k] == s[k]
    {
        res[i] := s[i];
        i := i + 1;
    }
}
// </vc-code>

