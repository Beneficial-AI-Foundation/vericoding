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
// Helper lemma might be needed for cyclic permutations
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
  res := s;
  var n := |s|;
  var m := n - n % 3;
  
  var i := 0;
  while i < m
    invariant 0 <= i <= m
    invariant |res| == n
    invariant forall j :: 0 <= j < i ==> 
      (j % 3 == 0 ==> res[j] == s[j+2]) &&
      (j % 3 == 1 ==> res[j] == s[j-1]) &&
      (j % 3 == 2 ==> res[j] == s[j-1])
    invariant forall j :: m <= j < n ==> res[j] == s[j]
  {
    if i % 3 == 0 {
      res := res[i := s[i+2]];
    } else if i % 3 == 1 {
      res := res[i := s[i-1]];
    } else {
      res := res[i := s[i-1]];
    }
    i := i + 1;
  }
}
// </vc-code>

