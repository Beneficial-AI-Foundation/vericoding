```vc-helpers
lemma NatBetweenIsEqual(i: int, t: int)
  requires i <= t < i + 1
  ensures t == i
{
  assert t <= i;
  assert i <= t;
  assert t == i;
}

lemma LeLtTrans(x:int, y:int, z:int)
  requires x <= y < z
  ensures x < z
{}
```

```vc-code
{
  var i: nat := 0;
  var w: nat := 0;
  r := false;
  while i <= n && !r
    invariant 0 <= i <= n + 1
    invariant r ==> 0 <= w <= n && n == cube(w)
    invariant !r ==> forall t: nat :: t < i ==> n != cube(t)
    decreases n - i + 1
  {
    if cube(i) == n {
      r := true;
      w := i;
    } else {
      assert forall t: nat | t < i + 1 :: n != cube(t) by {
        var t: nat;
        assume t < i + 1;
        if t < i {
          assert !r;
          assert n != cube(t);
        } else {
          assert i <= t;
          assert t < i + 1;
          NatBetweenIsEqual(i, t);
          assert t == i;
          assert n != cube(i);
        }
      }
      i := i + 1;
    }
  }
  if r {
    assert 0 <= w <= n && n == cube(w);
  } else {
    assert i > n;
    assert forall t: nat | t <= n :: n != cube(t) by {
      var t: nat;
      assume t <= n;
      assert !r;
      assert i > n;
      LeLtTrans(t, n, i);
      assert t < i;
      assert n != cube(t);
    }
  }
}
```