// 1 a)

// [ai, aj[
function sum(a: array<int>, i: int, j: int) : int
  requires 0 <= i <= j <= a.Length
  reads a
  decreases j
{
  if i == j then 0
  else a[j-1] + sum(a, i, j-1)
}

// 1 b)

// 1 c)
// a -> [1, 10, 3, −4, 5]
// c -> [0, 1, 11, 14, 10, 15]

predicate is_prefix_sum_for (a: array<int>, c: array<int>)
  reads c, a
{
  a.Length + 1 == c.Length && forall i: int :: 0 <= i <= a.Length ==> c[i] == sum(a, 0, i)
}

// <vc-helpers>
lemma sum_subrange(a: array<int>, i: int, j: int)
  requires 0 <= i <= j <= a.Length
  ensures sum(a, i, j) == sum(a, 0, j) - sum(a, 0, i)
  decreases j - i
{
  if i == j {
    assert sum(a, i, j) == 0;
    assert sum(a, 0, j) == sum(a, 0, i);
    calc {
      sum(a, i, j);
      == { assert sum(a, i, j) == 0; }
      0;
      == { assert sum(a, 0, j) == sum(a, 0, i); }
      sum(a, 0, j) - sum(a, 0, i);
    }
  } else {
    assert 0 < j;
    sum_subrange(a, i, j - 1);
    calc {
      sum(a, i, j);
      == { }
      a[j - 1] + sum(a, i, j - 1);
      == { sum_subrange(a, i, j - 1); }
      a[j - 1] + (sum(a, 0, j - 1) - sum(a, 0, i));
      == { }
      (a[j - 1] + sum(a, 0, j - 1)) - sum(a, 0, i);
      == { }
      sum(a, 0, j) - sum(a, 0, i);
    }
  }
}
// </vc-helpers>

// <vc-spec>
method queryFast(a: array<int>, c: array<int>, i: int, j: int) returns (r: int)
  requires 0 <= i <= j <= a.Length
  requires is_prefix_sum_for(a,c)
  ensures r == sum(a, i, j)
// </vc-spec>
// <vc-code>
{
  assert a.Length + 1 == c.Length;
  assert 0 <= i < c.Length;
  assert 0 <= j < c.Length;

  r := c[j] - c[i];

  assert 0 <= i <= a.Length;
  assert 0 <= j <= a.Length;
  assert c[i] == sum(a, 0, i);
  assert c[j] == sum(a, 0, j);

  sum_subrange(a, i, j);

  calc {
    r;
    == { }
    c[j] - c[i];
    == { assert c[j] == sum(a, 0, j); assert c[i] == sum(a, 0, i); }
    sum(a, 0, j) - sum(a, 0, i);
    == { sum_subrange(a, i, j); }
    sum(a, i, j);
  }
}
// </vc-code>

