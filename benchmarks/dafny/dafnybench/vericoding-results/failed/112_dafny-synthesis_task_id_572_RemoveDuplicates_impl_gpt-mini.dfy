

// <vc-helpers>
lemma AppendMembership(old: seq<int>, v: int)
  ensures free forall x :: x in old + [v] <==> (x in old || x == v)
{
}

lemma AppendMembershipFromInvariant(old: seq<int>, v: int, a: array<int>, i: int)
  requires a != null
  requires 0 <= i < a.Length
  requires v == a[i]
  requires forall x :: x in old <==> exists k :: 0 <= k < i && a[k] == x
  ensures free forall x :: (x in old || x == v) <==> exists k :: 0 <= k < i+1 && a[k] == x
{
}

lemma AppendPreservesUniqueness(old: seq<int>, v: int)
  requires forall p, q :: 0 <= p < q < old.Length ==> old[p] != old[q]
  requires !(v in old)
  ensures free forall p, q :: 0 <= p < q < old.Length + 1 ==> (old + [v])[p] != (old + [v])[q]
{
}
// </vc-helpers>

// <vc-spec>
method RemoveDuplicates(a: array<int>) returns (result: seq<int>)
    requires a != null
    ensures forall x :: x in result <==> exists i :: 0 <= i < a.Length && a[i] == x
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
// </vc-spec>
// <vc-code>
{
  var res: seq<int> := [];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall x :: x in res <==> exists k :: 0 <= k < i && a[k] == x
    invariant forall p, q :: 0 <= p < q < res.Length ==> res[p] != res[q]
  {
    var v := a[i];
    if !(v in res) {
      var oldRes := res;
      res := oldRes + [v];
      // membership of new res is either from oldRes or the new element v
      AppendMembership(oldRes, v);
      // by the loop invariant on oldRes and v = a[i], this equals existence in prefix 0..i
      AppendMembershipFromInvariant(oldRes, v, a, i);
      // combine the two facts to get the loop invariant for i+1
      assert forall x :: x in res <==> exists k :: 0 <= k < i+1 && a[k] == x;
      // uniqueness: v was not in oldRes, so appending preserves uniqueness
      AppendPreservesUniqueness(oldRes, v);
      assert forall p, q :: 0 <= p < q < res.Length ==> res[p] != res[q];
    }
    i := i + 1;
  }
  return res;
}
// </vc-code>

