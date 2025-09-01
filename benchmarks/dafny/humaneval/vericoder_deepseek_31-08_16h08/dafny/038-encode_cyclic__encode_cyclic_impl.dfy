

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

lemma modulo_properties(i: int)
    ensures i % 3 == 0 || i % 3 == 1 || i % 3 == 2
{
}

lemma encoding_invariant_helper(s: seq<int>, res: seq<int>, j: int, boundary: int)
    requires |res| == j
    requires j <= boundary
    requires boundary == |s| - |s| % 3
    requires forall k :: 0 <= k < j ==> 
        (k % 3 == 0 ==> res[k] == s[k + 1]) &&
        (k % 3 == 1 ==> res[k] == s[k + 1]) &&
        (k % 3 == 2 ==> res[k] == s[k - 2])
    ensures forall k :: 0 <= k < j ==> 
        (k % 3 == 0 ==> res[k] == s[k + 极]) &&
        (k % 3 == 1 ==> res[k] == s[k + 1]) &&
        (k % 3 == 2 ==> res[k] == s[k - 2])
{
}

lemma encoding_invariant_helper_extend(s: seq<int>, res: seq<int>, j: int, boundary: int)
    requires |res| == j
    requires j < boundary
    requires boundary == |s| - |s| % 3
    requires forall k :: 0 <= k < j ==> 
        (k % 3 == 0 ==> res[k] == s[k + 1]) &&
        (k % 3 == 1 ==> res[k] == s[k + 1]) &&
        (k % 3 == 2 ==> res[k] == s[k - 2])
    ensures forall k :: 0 <= k < j+1 ==> 
        (k % 3 == 0 ==> res[k] == s[k + 1]) &&
        (k % 3 == 1 ==> res[k] == s[k + 1]) &&
        (k % 3 == 2 ==> res[k] == s[k - 2])
{
    if j % 3 == 0 {
        assert res[j] == s[j + 1];
    } else if j % 3 == 1 {
        assert res[j] == s[j + 1];
    } else {
        assert res[j] == s[j - 2];
    }
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
        (k % 3 == 0 ==> res[k] == s[k + 1]) &&
        (k % 3 == 1 ==> res[k] == s[k + 1]) &&
        (k % 3 == 2 ==> res[k] == s[k - 2])
  {
    modulo_properties(j);
    var next_val: int;
    if j % 3 == 0 {
      next_val := s[j+1];
    } else if j % 3 == 1 {
      next_val := s[j+1];
    } else {
      next_val := s[j-2];
    }
    res := res + [next_val];
    encoding_invariant_helper_extend(s, res, j, boundary);
    j := j + 1;
  }
  while j < count
    invariant |res| == j
    invariant j <= count
    invariant j >= boundary
    invariant forall k :: boundary <= k < j ==> res[k] == s[k]
    invariant forall k :: 0 <= k < boundary ==> 
        (k % 3 == 0 ==> res[k] == s[k + 1]) &&
        (k % 3 == 1 ==> res[k] == s[k + 1]) &&
        (k % 3 == 2 ==> res[k] == s[k - 2])
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