predicate ValidInput(n: int, k: int, heights: seq<int>)
{
    n >= 1 && k >= 1 && |heights| == n && 
    forall i :: 0 <= i < |heights| ==> heights[i] >= 1
}

function CountEligible(heights: seq<int>, k: int): int
{
    |set i | 0 <= i < |heights| && heights[i] >= k :: i|
}

// <vc-helpers>
lemma CountEligibleAppend(h: seq<int>, x: int, k: int)
  ensures CountEligible(h + [x], k) == CountEligible(h, k) + (if x >= k then 1 else 0)
  decreases |h|
{
  var m := |h|;
  var S := set j | 0 <= j < m && h[j] >= k :: j;
  var T := set j | 0 <= j < m + 1 && (if j < m then h[j] >= k else x >= k) :: j;
  assert CountEligible(h, k) == |S|;
  assert CountEligible(h + [x], k) == |T|;

  if x >= k {
    // Show (S ∪ {m}) ⊆ T
    assert forall z :: (z in S || z == m) ==> z in T by {
      var z := _;
      if z in S {
        // z in S implies 0 <= z < m && h[z] >= k, hence z in T
        assert 0 <= z < m && h[z] >= k;
        assert 0 <= z < m + 1 && h[z] >= k;
        assert z in T;
      } else {
        // z == m, and x >= k, so m in T
        assert z == m;
        assert 0 <= m < m + 1 && x >= k;
        assert z in T;
      }
    }

    // Show T ⊆ (S ∪ {m})
    assert forall z :: z in T ==> (z in S || z == m) by {
      var z := _;
      // From z in T we get 0 <= z < m+1 and (if z < m then h[z] >= k else x >= k)
      assert 0 <= z < m + 1 && (if z < m then h[z] >= k else x >= k);
      if z < m {
        // then z in S
        assert z in S;
      } else {
        // then z == m
        assert z == m;
      }
    }

    // From mutual inclusion get equality
    assert T == S + (set j | j == m :: j);

    // m cannot be in S because S requires j < m
    assert !(m in S);

    // thus cardinality increases by 1
    assert |T| == |S| + 1;
  } else {
    // If x < k, then membership at index m would require x >= k, impossible.
    // So every element of T must come from S.
    assert forall z :: z in T ==> z in S by {
      var z := _;
      assert 0 <= z < m + 1 && (if z < m then h[z] >= k else x >= k);
      if z < m {
        assert z in S;
      } else {
        // z == m but then x >= k, contradicting x < k, so this case cannot happen
        assert false;
      }
    }

    // Hence sets are equal and cardinalities equal
    assert T == S;
    assert |T| == |S|;
  }

  // Conclude the required equality using the computed cardinalities
  assert CountEligible(h + [x], k) == |T|;
  assert CountEligible(h, k) == |S|;
  assert CountEligible(h + [x], k) == CountEligible(h, k) + (if x >= k then 1 else 0);
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, heights: seq<int>) returns (count: int)
    requires ValidInput(n, k, heights)
    ensures 0 <= count <= |heights|
    ensures count == CountEligible(heights, k)
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var c := 0;
  while i < n
    invariant 0 <= i <= n
    invariant 0 <= c <= i
    invariant c == CountEligible(heights[..i], k)
    decreases n - i
  {
    if heights[i] >= k {
      c := c + 1;
    }
    // Update the lemma-based fact about counts after appending heights[i]
    CountEligibleAppend(heights[..i], heights[i], k);
    assert c == CountEligible(heights[..i + 1], k);
    i := i + 1;
  }
  count := c;
}
// </vc-code>

