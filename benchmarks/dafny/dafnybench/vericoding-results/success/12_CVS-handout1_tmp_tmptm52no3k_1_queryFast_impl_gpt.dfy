/*                                      Cumulative Sums over Arrays                                        */

/*
    Daniel Cavalheiro   57869
    Pedro Nunes         57854
*/



//(a)

function sum(a: array<int>, i: int, j: int): int
    reads a
    requires 0 <= i <= j <= a.Length
    decreases j - i
{
    if (i == j) then 0
    else a[i] + sum(a, i+1, j)
}



//(b)




//(c)

predicate is_prefix_sum_for (a: array<int>, c: array<int>)
    requires a.Length + 1 == c.Length
    requires c[0] == 0
    reads c, a
{
    forall i: int :: 0 <= i < a.Length ==> c[i+1] == c[i] + a[i]
}

// <vc-helpers>
lemma minus_subst(x:int, y:int, z:int)
  ensures x - (y - z) == (x - y) + z
{ }

lemma sum_unfold(a: array<int>, i: int, j: int)
  requires 0 <= i <= j <= a.Length
  ensures i == j ==> sum(a, i, j) == 0
  ensures i < j ==> sum(a, i, j) == a[i] + sum(a, i+1, j)
{
  if i == j {
  } else {
  }
}

lemma segmentSumFromPrefix(a: array<int>, c: array<int>, i: int, j: int)
  requires a.Length + 1 == c.Length
  requires c[0] == 0
  requires is_prefix_sum_for(a, c)
  requires 0 <= i <= j <= a.Length
  ensures c[j] - c[i] == sum(a, i, j)
  decreases j - i
{
  if i == j {
  } else {
    assert 0 <= i < a.Length;
    assert 0 <= i < c.Length;
    assert 0 <= i + 1 < c.Length;
    assert 0 <= j <= a.Length;
    assert 0 <= j < c.Length;

    assert c[i+1] == c[i] + a[i];
    segmentSumFromPrefix(a, c, i+1, j);
    calc {
      c[j] - c[i];
      == { assert c[i] == c[i+1] - a[i]; }
      c[j] - (c[i+1] - a[i]);
      == { minus_subst(c[j], c[i+1], a[i]); }
      (c[j] - c[i+1]) + a[i];
      == { assert c[j] - c[i+1] == sum(a, i+1, j); }
      sum(a, i+1, j) + a[i];
      == { }
      a[i] + sum(a, i+1, j);
      == { sum_unfold(a, i, j); }
      sum(a, i, j);
    }
  }
}
// </vc-helpers>

// <vc-spec>
method queryFast(a: array<int>, c: array<int>, i: int, j: int) returns (r: int)
    requires a.Length + 1 == c.Length && c[0] == 0
    requires 0 <= i <= j <= a.Length
    requires is_prefix_sum_for(a,c)  
    ensures r == sum(a, i, j)
// </vc-spec>
// <vc-code>
{
  segmentSumFromPrefix(a, c, i, j);
  assert 0 <= i < c.Length;
  assert 0 <= j < c.Length;
  r := c[j] - c[i];
}
// </vc-code>

