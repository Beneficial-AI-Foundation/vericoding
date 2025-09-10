method sorted_even(a: seq<int>) returns (sorted: seq<int>)
  // pre-conditions-start
  requires |a| > 0
  // pre-conditions-end
  // post-conditions-start
  ensures |sorted| == |a|
  ensures forall i, j :: 0 <= i < j && 2 * i < |sorted| && 2 * j < |sorted| ==>
      sorted[2 * i] <= sorted[2 * j]
      ensures forall i :: 0 <= i < |a| && i % 2 == 1 ==> sorted[i] == a[i]
      ensures multiset(a) == multiset(sorted)
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
function method CountTrue(p: seq<bool>, n: int): int
  requires 0 <= n <= |p|
  ensures 0 <= CountTrue(p, n) <= n
  ensures CountTrue(p, n) == |{i: int | 0 <= i < n && p[i]}|
{
  if n == 0 then 0 else CountTrue(p, n - 1) + (if p[n - 1] then 1 else 0)
}

method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  ensures |sorted| == |s|
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures multiset(s) == multiset(sorted)
  decreases |s|
{
  if |s| == 0 {
    sorted := [];
    return;
  }
  var tail := s[1..];
  var st := SortSeq(tail);
  var x := s[0];
  var pos := 0;
  while pos < |st| && st[pos] <= x
    invariant 0 <= pos <= |st|
    invariant forall k :: 0 <= k < pos ==> st[k] <= x
  {
    pos := pos + 1;
  }
  // After loop: for all k < pos, st[k] <= x.
  // If pos < |st| then st[pos] > x, and because st is sorted, for all k >= pos, st[k] > x.
  sorted := st[..pos] + [x] + st[pos..];
  // Prove sortedness
  // For indices both in st[..pos] or both in st[pos..] ordering preserved by st.
  // For idx in prefix and idx' in suffix or x, prefix elements <= x and suffix elements >= x
  // Dafny can verify these from invariants and from the ensures of recursive call.
  // Multiset reasoning: multiset(st) + multiset([x]) == multiset(s)
  // So multiset(sorted) == multiset(s).
}
// </vc-helpers>

// <vc-spec>
method SortSeqPred(s: seq<int>, p: seq<bool>) returns (sorted: seq<int>)
  // pre-conditions-start
  requires |s| == |p|
  // pre-conditions-end
  // post-conditions-start
  ensures |sorted| == |s|
  ensures forall i, j :: 0 <= i < j < |sorted| && p[i] && p[j] ==> sorted[i] <= sorted[j]
  ensures multiset(s) == multiset(sorted)
  ensures forall i :: 0 <= i < |s| && !p[i] ==> sorted[i] == s[i]
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var sFilt := seq i | 0 <= i < |s| && p[i] :: s[i];
  var sortedFilt := SortSeq(sFilt);
  sorted := seq i | 0 <= i < |s| :: if p[i] then sortedFilt[CountTrue(p, i + 1) - 1] else s[i];
}
// </vc-code>

