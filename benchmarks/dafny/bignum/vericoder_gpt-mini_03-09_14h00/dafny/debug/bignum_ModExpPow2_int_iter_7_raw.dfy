```vc-helpers
lemma {:axiom} Exp_add(a:nat, b:nat, c:nat)
  ensures Exp_int(a, b + c) == Exp_int(a, b) * Exp_int(a, c)
{ }

lemma {:opaque} Exp2_dbl(i: nat)
  ensures Exp_int(2, i+1) == Exp_int(2, i) + Exp_int(2, i)
  decreases i
{
  assert Exp_int(2, i+1) == 2 * Exp_int(2, i);
  assert 2 * Exp_int(2, i) == Exp_int(2, i) + Exp_int(2, i);
}
```

```vc-code
{
  var r: nat := x % z;
  var i: nat := 0;
  while i < n
    invariant 0 <= i <= n
    invariant 0 <= r < z
    invariant r % z == Exp_int(x, Exp_int(2, i)) % z
    decreases n - i
  {
    var r_old := r;
    r := (r_old * r_old) % z;
    assert 0 <= r < z;
    assert r % z == (r_old * r_old) % z;
    assert r % z == ((Exp_int(x, Exp_int(2, i)) % z) * (Exp_int(x, Exp_int(2, i)) % z)) % z;
    assert r % z == (Exp_int(x, Exp_int(2, i)) * Exp_int(x, Exp_int(2, i))) % z;
    Exp2_dbl(i);
    Exp_add(x, Exp_int(2, i), Exp_int(2, i));
    assert Exp_int(x, Exp_int(2, i) + Exp_int(2, i)) == Exp_int(x, Exp_int(2, i)) * Exp_int(x, Exp_int(2, i));
    assert Exp_int(2, i+1) == Exp_int(2, i) + Exp_int(2, i);
    assert r % z == Exp_int(x, Exp_int(2, i+1)) % z;
    i := i + 1;
  }
  assert r == r % z;
  assert r % z == Exp_int(x, Exp_int(2, n)) % z;
  res := r;
}
```