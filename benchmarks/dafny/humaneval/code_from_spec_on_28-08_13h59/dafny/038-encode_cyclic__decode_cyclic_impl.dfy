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

// <vc-description>
/*
function_signature: method decode_cyclic(s: seq<int>) returns (res: seq<int>)
Decode data. Ensures: returns the correct size/count; the condition holds for all values; the condition holds for all values; the condition holds for all values.
*/
// </vc-description>

// <vc-spec>
method decode_cyclic(s: seq<int>) returns (res: seq<int>)
    ensures |s| == |res|
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 0 ==> res[i + 1] == s[i])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 1 ==> res[i + 1] == s[i])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 2 ==> res[i - 2] == s[i])
    ensures forall i :: |s| - |s| % 3 <= i < |s| ==> (res[i] == s[i])
// </vc-spec>
// <vc-code>
{
    res := s;
    var len := |s|;
    var groups := len / 3;
    
    var i := 0;
    while i < groups
        invariant 0 <= i <= groups
        invariant |res| == |s|
        invariant forall j :: 0 <= j < i * 3 ==> (j % 3 == 0 ==> res[j + 1] == s[j])
        invariant forall j :: 0 <= j < i * 3 ==> (j % 3 == 1 ==> res[j + 1] == s[j])
        invariant forall j :: 0 <= j < i * 3 ==> (j % 3 == 2 ==> res[j - 2] == s[j])
        invariant forall j :: i * 3 <= j < |s| ==> res[j] == s[j]
    {
        var base := i * 3;
        if base + 2 < len {
            var temp0 := res[base];
            var temp1 := res[base + 1];
            var temp2 := res[base + 2];
            
            res := res[base := temp2];
            res := res[base + 1 := temp0];
            res := res[base + 2 := temp1];
        }
        i := i + 1;
    }
}
// </vc-code>
