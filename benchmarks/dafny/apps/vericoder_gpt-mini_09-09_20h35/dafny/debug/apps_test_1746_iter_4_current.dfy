function hasChildren(node: int, parents: seq<int>, n: int): bool
    requires 0 <= node < n
    requires n >= 3
    requires |parents| == n - 1
{
    exists i :: 0 <= i < n - 1 && parents[i] - 1 == node
}

function countLeafChildren(node: int, parents: seq<int>, n: int): int
    requires 0 <= node < n
    requires n >= 3
    requires |parents| == n - 1
{
    |set i | 0 <= i < n - 1 && parents[i] - 1 == node && !hasChildren(i + 1, parents, n)|
}

predicate ValidInput(n: int, parents: seq<int>)
{
    n >= 3 && |parents| == n - 1 && 
    (forall i :: 0 <= i < n - 1 ==> 1 <= parents[i] <= i + 1)
}

predicate IsSpruce(n: int, parents: seq<int>)
    requires ValidInput(n, parents)
{
    forall node :: 0 <= node < n && hasChildren(node, parents, n) ==> 
        countLeafChildren(node, parents, n) >= 3
}

// <vc-helpers>
// No helpers needed for this solution.
// </vc-helpers>

// <vc-spec>
method solve(n: int, parents: seq<int>) returns (result: string)
    requires ValidInput(n, parents)
    ensures result == "Yes" || result == "No"
    ensures result == "Yes" <==> IsSpruce(n, parents)
// </vc-spec>
// <vc-code>
{
  var leafCounts := new int[n];
  var ok := true;
  var node := 0;
  ghost var badIndex := -1;
  ghost var badCount := 0;
  while node < n
    decreases n - node
    invariant 0 <= node <= n
    invariant forall k :: 0 <= k < node ==> leafCounts[k] == countLeafChildren(k, parents, n)
    invariant ok ==> (forall k :: 0 <= k < node && hasChildren(k, parents, n) ==> leafCounts[k] >= 3)
  {
    var cnt := 0;
    var hasChild := false;
    var i := 0;
    while i < n - 1
      decreases (n - 1) - i
      invariant 0 <= i <= n - 1
      invariant cnt == |set j | 0 <= j < i && parents[j] - 1 == node && !hasChildren(j + 1, parents, n)|
      invariant hasChild == (exists j :: 0 <= j < i && parents[j] - 1 == node)
    {
      if parents[i] - 1 == node {
        hasChild := true;
        var child := i + 1;
        var kk := 0;
        var childHasChild := false;
        while kk < n - 1
          decreases (n - 1) - kk
          invariant 0 <= kk <= n - 1
          invariant childHasChild == (exists j :: 0 <= j < kk && parents[j] - 1 == child)
        {
          if parents[kk] - 1 == child {
            childHasChild := true;
            break;
          }
          kk := kk + 1;
        }
        assert childHasChild == hasChildren(child, parents, n);
        if !childHasChild {
          cnt := cnt + 1;
        }
      }
      i := i + 1;
    }
    leafCounts[node] := cnt;
    if hasChild && cnt < 3 {
      assert cnt == countLeafChildren(node, parents, n);
      ghost badIndex := node;
      ghost badCount := cnt;
      ok := false;
      break;
    }
    node := node + 1;
  }

  if ok {
    result := "Yes";
  } else {
    result := "No";
  }

  if ok {
    ghost var nd := 0;
    while nd < n
      decreases n - nd
    {
      if hasChildren(nd, parents, n) {
        assert leafCounts[nd] == countLeafChildren(nd, parents, n);
        assert leafCounts[nd] >= 3;
      }
      nd := nd + 1;
    }
    assert IsSpruce(n, parents);
  } else {
    assert 0 <= badIndex < n;
    ghost var bad := badIndex;
    ghost var c2 := 0;
    var ii := 0;
    while ii < n - 1
      decreases (n - 1) - ii
      invariant 0 <= ii <= n - 1
      invariant c2 == |set j | 0 <= j < ii && parents[j] - 1 == bad && !hasChildren(j + 1, parents, n)|
    {
      if parents[ii] - 1 == bad {
        var ch := ii + 1;
        var jj := 0;
        var chHasChild := false;
        while jj < n - 1
          decreases (n - 1) - jj
          invariant 0 <= jj <= n - 1
          invariant chHasChild == (exists k :: 0 <= k < jj && parents[k] - 1 == ch)
        {
          if parents[jj] - 1 == ch {
            chHasChild := true;
            break;
          }
          jj := jj + 1;
        }
        assert chHasChild == hasChildren(ch, parents, n);
        if !chHasChild {
          c2 := c2 + 1;
        }
      }
      ii := ii + 1;
    }
    assert c2 == countLeafChildren(bad, parents, n);
    assert c2 < 3;
    assert leafCounts[bad] == badCount;
    assert badCount == countLeafChildren(bad, parents, n);
    assert exists node :: 0 <= node < n && hasChildren(node, parents, n) && countLeafChildren(node, parents, n) < 3;
    assert !IsSpruce(n, parents);
  }
}
// </vc-code>

