// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function SeqContains(s: seq<int>, x: int): bool { exists i :: 0 <= i < |s| && s[i] == x }
// </vc-helpers>

// <vc-spec>
method SharedElements(list1: array<int>, list2: array<int>) returns (shared: array<int>)
    ensures
        forall i :: 0 <= i < shared.Length ==> (shared[i] in list1[..] && shared[i] in list2[..])
    ensures
        forall i, j :: 0 <= i < j < shared.Length ==> shared[i] != shared[j]
// </vc-spec>
// <vc-code>
{
  var n1 := list1.Length;
  var n2 := list2.Length;
  var res: seq<int> := [];
  var i := 0;
  while i < n1
    invariant 0 <= i <= n1
    invariant forall k :: 0 <= k < |res| ==> res[k] in list1[..] && res[k] in list2[..]
    invariant forall p, q :: 0 <= p < q < |res| ==> res[p] != res[q]
    decreases n1 - i
  {
    var v := list1[i];
    if SeqContains(res, v) {
      // already recorded
    } else {
      var j := 0;
      var found := false;
      while j < n2
        invariant 0 <= j <= n2
        invariant found ==> exists jj :: 0 <= jj < j && list2[jj] == v
        decreases n2 - j
      {
        if list2[j] == v {
          found := true;
          j := n2;
        } else {
          j := j + 1;
        }
      }
      if found {
        res := res + [v];
      }
    }
    i := i + 1;
  }

  shared := new int[|res|];
  var k := 0;
  while k < |res|
    invariant 0 <= k <= |res|
    invariant shared.Length == |res|
    invariant forall t :: 0 <= t < k ==> shared[t] == res[t]
    decreases |res| - k
  {
    shared[k] := res[k];
    k := k + 1;
  }
}
// </vc-code>
