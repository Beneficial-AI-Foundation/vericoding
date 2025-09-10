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
  while node < n
    decreases n - node
  {
    var cnt := 0;
    var hasChild := false;
    var i := 0;
    while i < n - 1
      decreases (n - 1) - i
    {
      if parents[i] - 1 == node {
        hasChild := true;
        var child := i + 1;
        var kk := 0;
        var childHasChild := false;
        while kk < n - 1
          decreases (n - 1) - kk
        {
          if parents[kk] - 1 == child {
            childHasChild := true;
            break;
          }
          kk := kk + 1;
        }
        if !childHasChild {
          cnt := cnt + 1;
        }
      }
      i := i + 1;
    }
    leafCounts[node] := cnt;
    if hasChild && cnt < 3 {
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

  ghost {
    // Show equivalence between computed ok and predicate IsSpruce
    if ok {
      // Prove IsSpruce: for every node with children, countLeafChildren >= 3
      var nd := 0;
      while nd < n
        decreases n - nd
      {
        if hasChildren(nd, parents, n) {
          // Recompute count by iterating and show equality with countLeafChildren
          var c := 0;
          var ii := 0;
          while ii < n - 1
            decreases (n - 1) - ii
          {
            if parents[ii] - 1 == nd {
              var ch := ii + 1;
              var jj := 0;
              var chHasChild := false;
              while jj < n - 1
                decreases (n - 1) - jj
              {
                if parents[jj] - 1 == ch {
                  chHasChild := true;
                  break;
                }
                jj := jj + 1;
              }
              if !chHasChild {
                c := c + 1;
              }
            }
            ii := ii + 1;
          }
          // c is the number of leaf-children of nd
          assert c == countLeafChildren(nd, parents, n);
          // From runtime computation we must have stored leafCounts[nd] >= 3
          assert leafCounts[nd] >= 3;
          assert c == leafCounts[nd];
          assert c >= 3;
        }
        nd := nd + 1;
      }
      assert IsSpruce(n, parents);
    } else {
      // ok == false, find a node witnessing violation
      var bad := -1;
      var idx := 0;
      while idx < n
        decreases n - idx
      {
        if 0 <= idx < n && hasChildren(idx, parents, n) && leafCounts[idx] < 3 {
          bad := idx;
          break;
        }
        idx := idx + 1;
      }
      if bad >= 0 {
        // Recompute count for bad to relate to countLeafChildren
        var c2 := 0;
        var ii := 0;
        while ii < n - 1
          decreases (n - 1) - ii
        {
          if parents[ii] - 1 == bad {
            var ch := ii + 1;
            var jj := 0;
            var chHasChild := false;
            while jj < n - 1
              decreases (n - 1) - jj
            {
              if parents[jj] - 1 == ch {
                chHasChild := true;
                break;
              }
              jj := jj + 1;
            }
            if !chHasChild {
              c2 := c2 + 1;
            }
          }
          ii := ii + 1;
        }
        assert c2 == leafCounts[bad];
        assert c2 < 3;
        assert countLeafChildren(bad, parents, n) == c2;
        assert exists node :: 0 <= node < n && hasChildren(node, parents, n) && countLeafChildren(node, parents, n) < 3;
        assert !IsSpruce(n, parents);
      } else {
        // Should be unreachable: ok == false implies such a bad node exists
        assert false;
      }
    }
  }
}
// </vc-code>

