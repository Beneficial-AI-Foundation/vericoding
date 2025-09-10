predicate ValidInput(n: int, v: int, sellers: seq<seq<int>>) {
    n >= 0 && v >= 0 && |sellers| == n && 
    forall i :: 0 <= i < |sellers| ==> |sellers[i]| > 0
}

predicate ValidOutput(count: int, indices: seq<int>, n: int) {
    count == |indices| && count >= 0 && count <= n &&
    (forall i :: 0 <= i < |indices| ==> 1 <= indices[i] <= n) &&
    (forall i :: 0 <= i < |indices| - 1 ==> indices[i] < indices[i+1])
}

predicate CorrectSolution(v: int, sellers: seq<seq<int>>, indices: seq<int>) 
    requires forall i :: 0 <= i < |sellers| ==> |sellers[i]| > 0
    requires forall i :: 0 <= i < |indices| ==> 1 <= indices[i] <= |sellers|
{
    (forall i :: 0 <= i < |indices| ==> v > Min(sellers[indices[i] - 1])) &&
    (forall i :: 0 <= i < |sellers| ==> (v > Min(sellers[i]) <==> (i + 1) in indices))
}

// <vc-helpers>
function Min(s: seq<int>): int
    requires |s| > 0
    decreases |s|
{
    if |s| == 1 then s[0] else var m := Min(s[1..]); if s[0] <= m then s[0] else m
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, v: int, sellers: seq<seq<int>>) returns (count: int, indices: seq<int>)
    requires ValidInput(n, v, sellers)
    ensures ValidOutput(count, indices, n)
    ensures CorrectSolution(v, sellers, indices)
// </vc-spec>
// <vc-code>
{
  var res: seq<int> := [];
  var i := 0;
  // help the verifier establish the quantified invariant at loop entry
  assert i == 0;
  assert forall j :: 0 <= j < i ==> (v > Min(sellers[j])) <==> ((j+1) in res);
  while i < n
    invariant 0 <= i <= n
    invariant |res| <= i
    invariant forall t :: 0 <= t < |res| ==> 1 <= res[t] <= i
    invariant forall t :: 0 <= t < |res| - 1 ==> res[t] < res[t+1]
    invariant |sellers| == n
    invariant forall k :: 0 <= k < n ==> |sellers[k]| > 0
    invariant forall j :: 0 <= j < i ==> (v > Min(sellers[j])) <==> ((j+1) in res)
  {
    if v > Min(sellers[i]) {
      res := res + [i + 1];
    }
    i := i + 1;
  }
  count := |res|;
  indices := res;
}
// </vc-code>

