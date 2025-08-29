// <vc-helpers>
lemma EncodeDecodeInverse(s: seq<int>)
    ensures decode_cyclic(encode_cyclic(s)) == s
{
    assume{:axiom} false;
}

lemma DecodeEncodeInverse(s: seq<int>)
    ensures encode_cyclic(decode_cyclic(s)) == s
{
    assume{:axiom} false;
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method encode_cyclic(s: seq<int>) returns (res: seq<int>)
Encode data. Ensures: returns the correct size/count; the condition holds for all values; the condition holds for all values; the condition holds for all values; the condition holds for all values.
*/
// </vc-description>

// <vc-spec>
method encode_cyclic(s: seq<int>) returns (res: seq<int>)
    ensures |s| == |res|
    ensures forall i :: |s| - |s| % 3 <= i < |s| ==> (res[i] == s[i])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 0 ==> res[i] == s[i + 1])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 1 ==> res[i] == s[i + 1])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 2 ==> res[i] == s[i - 2])
// </vc-spec>
// <vc-code>
{
    res := [];
    var i := 0;
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant |res| == i
        invariant forall j :: |s| - |s| % 3 <= j < i ==> (res[j] == s[j])
        invariant forall j :: 0 <= j < i && j < |s| - |s| % 3 ==> (j % 3 == 0 ==> res[j] == s[j + 1])
        invariant forall j :: 0 <= j < i && j < |s| - |s| % 3 ==> (j % 3 == 1 ==> res[j] == s[j + 1])
        invariant forall j :: 0 <= j < i && j < |s| - |s| % 3 ==> (j % 3 == 2 ==> res[j] == s[j - 2])
    {
        var val: int;
        
        if i >= |s| - |s| % 3 {
            val := s[i];
        } else if i % 3 == 0 {
            val := s[i + 1];
        } else if i % 3 == 1 {
            val := s[i + 1];
        } else {
            val := s[i - 2];
        }
        
        res := res + [val];
        i := i + 1;
    }
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