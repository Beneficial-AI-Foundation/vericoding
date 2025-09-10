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
function Min(a: seq<int>): int
  requires |a| > 0
  decreases |a|
{
  if |a| == 1 then a[0]
  else {
    var m := Min(a[1..]);
    if a[0] < m then a[0] else m
  }
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
    var indices_seq: seq<int> := [];
    if n == 0 {
        count := 0;
        indices := [];
        return;
    }
    for i := 0 to n-1
        invariant 0 <= i <= n
        invariant forall k :: 0 <= k < |indices_seq| ==> 1 <= indices_seq[k] <= n && indices_seq[k] - 1 < i
        invariant |indices_seq| >= 0 && |indices_seq| <= i
        invariant forall m :: 0 <= m < i ==> (v > Min(sellers[m]) <==> m+1 in indices_seq)
        invariant forall k1, k2 :: 0 <= k1 < k2 < |indices_seq| ==> indices_seq[k1] < indices_seq[k2]
    {
        if v > Min(sellers[i])
        {
            indices_seq := indices_seq + [i+1];
        }
    }
    count := |indices_seq|;
    indices := indices_seq;
}
// </vc-code>

