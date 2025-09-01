

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method encode_cyclic(s: seq<int>) returns (res: seq<int>) 
    // post-conditions-start
    ensures |s| == |res|
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 0 ==> res[i] == s[i + 1])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 1 ==> res[i] == s[i + 1])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 2 ==> res[i] == s[i - 2])
    ensures forall i :: |s| - |s| % 3 <= i < |s| ==> (res[i] == s[i])
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    var n := |s|;
    var m := n - n % 3;
    var arr := new int[n];
    
    for i := 0 to n
        invariant forall j :: 0 <= j < i ==> 
            (j < m ==> 
                (j % 3 == 0 ==> arr[j] == s[j+1]) &&
                (j % 3 == 1 ==> arr[j] == s[j+1]) &&
                (j % 3 == 2 ==> arr[j] == s[j-2])
            ) &&
            (j >= m ==> arr[j] == s[j])
    {
        if i < m {
            if i % 3 == 0 {
                arr[i] := s[i + 1];
            } else if i % 3 == 1 {
                arr[i] := s[i + 1];
            } else {
                arr[i] := s[i - 2];
            }
        } else {
            arr[i] := s[i];
        }
    }
    res := arr[..];
}
// </vc-code>

method decode_cyclic(s: seq<int>) returns (res: seq<int>)
    // post-conditions-start
    ensures |s| == |res|
    ensures forall i :: |s| - |s| % 3 <= i < |s| ==> (res[i] == s[i])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 0 ==> res[i] == s[i + 2])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 1 ==> res[i] == s[i - 1])
    // post-conditions-end
{
  assume{:axiom} false;
}