

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
var res : seq<int> := [];
var handled_len := |s| - |s| % 3;
var i := 0;
while i < |s|
  invariant |res| == i
  invariant i <= |s|
  invariant handled_len == |s| - |s| % 3
  invariant forall k :: 0 <= k < i ==> 
    k < handled_len ==> 
      if k % 3 == 0 then res[k] == s[k+1] 
      else if k % 3 == 1 then res[k] == s[k+1] 
      else res[k] == s[k-2]
    else res[k] == s[k]
{
  if i < handled_len {
    if i % 3 == 0 { res := res + [s[i+1]]; }
    else if i % 3 == 1 { res := res + [s[i+1]]; }
    else { res := res + [s[i-2]]; }
  } else {
    res := res + [s[i]];
  }
  i := i + 1;
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