function seq_min(s: seq<int>): int
    requires |s| > 0
    ensures seq_min(s) in s
    ensures forall k :: 0 <= k < |s| ==> seq_min(s) <= s[k]
{
    if |s| == 1 then s[0]
    else if s[0] <= seq_min(s[1..]) then s[0]
    else seq_min(s[1..])
}

predicate ValidInput(arr: seq<int>)
{
    |arr| >= 2 && 
    exists i, j :: 0 <= i < j < |arr| && arr[i] == arr[j] == seq_min(arr)
}

// <vc-helpers>
// No additional helper code required.
// </vc-helpers>

// <vc-spec>
method solve(arr: seq<int>) returns (result: int)
    requires ValidInput(arr)
    ensures result > 0
    ensures result <= |arr| - 1
    ensures exists i, j :: 0 <= i < j < |arr| && arr[i] == arr[j] == seq_min(arr) && j - i == result
    ensures forall i, j :: 0 <= i < j < |arr| && arr[i] == arr[j] == seq_min(arr) ==> j - i >= result
// </vc-spec>
// <vc-code>
{
  var n := |arr|;
  var m := seq_min(arr);

  var idx := 0;
  while idx < n && arr[idx] != m
    decreases n - idx
    invariant 0 <= idx <= n
    invariant forall k :: 0 <= k < idx ==> arr[k] != m
  {
    idx := idx + 1;
  }
  assert idx < n;
  var first := idx;
  assert arr[first] == m;

  var prev := first;
  var i := prev + 1;
  var res := n;
  ghost var bestA := -1;
  ghost var bestB := -1;

  while i < n
    decreases n - i
    invariant 0 <= i <= n
    invariant 0 <= prev < n
    invariant first <= prev < i <= n
    invariant arr[prev] == m
    invariant forall k :: prev < k < i ==> arr[k] != m
    invariant forall a, b :: first <= a < b < i && arr[a] == arr[b] == m ==> b - a >= res
    invariant (bestA == -1 && bestB == -1) <==> (res == n)
    invariant (bestA == -1 && bestB == -1) || (0 <= bestA < bestB < i && arr[bestA] == arr[bestB] == m && bestB - bestA == res)
    invariant res == n || res >= 1
  {
    if arr[i] == m {
      var d := i - prev;
      if d < res {
        res := d;
        bestA := prev;
        bestB := i;
      }
      prev := i;
    }
    i := i + 1;
  }

  // Prove there is some pair after 'first', hence res < n.
  ghost var a, b :| 0 <= a < b < n && arr[a] == arr[b] == m;
  // From the earlier scan, no index < first has value m.
  assert forall k :: 0 <= k < first ==> arr[k] != m;
  // Thus the chosen 'a' must satisfy a >= first.
  assert a >= first;
  // From the loop invariant at termination (i == n), we have b - a >= res.
  assert b - a >= res;
  assert b - a < n;
  assert res < n;

  // From invariant res==n <==> bestA==-1 && bestB==-1 and res < n, we get bestA/b set.
  assert !(bestA == -1 && bestB == -1);
  // bestB - bestA == res
  assert 0 <= bestA < bestB < n;
  assert arr[bestA] == m && arr[bestB] == m;
  assert bestB - bestA == res;

  result := res;
}
// </vc-code>

