

// <vc-helpers>
lemma cyclic_encoding_lemma(s: seq<int>, res: seq<int>, i: int)
    requires |s| == |res|
    requires 0 <= i < |s| - |s| % 3
    ensures (i % 3 == 0 ==> res[i] == s[i + 1])
    ensures (i % 3 == 1 ==> res[i] == s[i + 1]) 
    ensures (i % 3 == 2 ==> res[i] == s[i - 2])
{
}

lemma cyclic_decoding_lemma(s: seq<int>, res: seq<int>, i: int)
    requires |s| == |res|
    requires 0 <= i < |s| - |s| % 3
    ensures (i % 3 == 0 ==> res[i] == s[i + 2])
    ensures (i % 3 == 1 ==> res[i] == s[i - 1]) 
{
}
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
  res := [];
  var count := |s|;
  var rem := count % 3;
  var boundary := count - rem;
  var j := 0;
  while j < boundary
    invariant |res| == j
    invariant j <= boundary
    invariant forall k :: 0 <= k < j ==> 
        (k%3==0 ==> res[k] == s[k+1]) &&
        (k%3==1 ==> res[k] == s[k+1]) &&
        (k%3==2 ==> res[k] == s[k-2])
  {
    if j % 3 == 0 {
      res := res + [s[j+1]];
    } else if j % 3 == 1 {
      res := res + [s[j+1]];
    } else {
      res := res + [s[j-2]];
    }
    j := j + 1;
  }
  while j < count
    invariant |res| == j
    invariant j <= count
    invariant j >= boundary
    invariant forall k :: boundary <= k < j ==> res[k] == s[k]
  {
    res := res + [s[j]];
    j := j + 1;
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