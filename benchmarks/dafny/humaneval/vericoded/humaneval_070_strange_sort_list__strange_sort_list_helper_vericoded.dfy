// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma EvenIndexBound(n: int, i: int)
  requires n >= 0 && 0 <= i < n && i % 2 == 0
  ensures 0 <= i/2 < n
{
  assert 0 <= i/2;
  assert i/2 <= i;
  assert i < n;
  assert i/2 < n;
}

lemma OddIndexBound(n: int, i: int)
  requires n >= 0 && 0 <= i < n && i % 2 == 1
  ensures 0 <= n - (i - 1)/2 - 1 < n
{
  var k := (i - 1) / 2;
  assert 0 <= k <= i - 1;
  assert i - 1 < n;
  // k <= i-1 implies n - k - 1 >= n - (i - 1) - 1
  assert n - k - 1 >= n - (i - 1) - 1;
  assert n - (i - 1) - 1 == n - i;
  assert n - i > 0;
  assert n - k - 1 > 0;
  assert n - k - 1 <= n - 1;
  assert n - k - 1 < n;
}

// </vc-helpers>

// <vc-spec>
method strange_sort_list_helper(s: seq<int>) returns (sorted: seq<int>, strange: seq<int>)

    ensures multiset(s) == multiset(sorted)
    ensures |s| == |sorted| == |strange|
    ensures forall i :: 0 <= i < |s| && i % 2 == 0 ==> strange[i] == sorted[i / 2]
    ensures forall i :: 0 <= i < |s| && i % 2 == 1 ==> strange[i] == sorted[|s| - (i - 1) / 2 - 1]
// </vc-spec>
// <vc-code>
{
  sorted := s;
  strange := [];
  var n := |s|;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |strange| == i
    invariant forall j :: 0 <= j < |strange| && j % 2 == 0 ==> strange[j] == sorted[j/2]
    invariant forall j :: 0 <= j < |strange| && j % 2 == 1 ==> strange[j] == sorted[n - (j - 1)/2 - 1]
  {
    if i % 2 == 0 {
      var idx := i / 2;
      strange := strange + [sorted[idx]];
    } else {
      var idx := n - (i - 1) / 2 - 1;
      strange := strange + [sorted[idx]];
    }
    i := i + 1;
  }
}

// </vc-code>
