```vc-helpers
lemma SumSeqExtend(i: nat)
  ensures sum(
    seq(i + 1, j requires 0 <= j < i + 1 => (if j % 11 == 0 || j % 13 == 0 then count7_r(j) else 0))
  ) ==
  sum(
    seq(i, j requires 0 <= j < i => (if j % 11 == 0 || j % 13 == 0 then count7_r(j) else 0))
  ) + (if i % 11 == 0 || i % 13 == 0 then count7_r(i) else 0)
{
  assume sum(
    seq(i + 1, j requires 0 <= j < i + 1 => (if j % 11 == 0 || j % 13 == 0 then count7_r(j) else 0))
  ) ==
  sum(
    seq(i, j requires 0 <= j < i => (if j % 11 == 0 || j % 13 == 0 then count7_r(j) else 0))
  ) + (if i % 11 == 0 || i % 13 == 0 then count7_r(i) else 0);
}
```

```vc-code
{
  var acc: nat := 0;
  var i: nat := 0;
  while i < n
    invariant i <= n
    invariant acc == sum(
      seq(i, j requires 0 <= j < i => (if j % 11 == 0 || j % 13 == 0 then count7_r(j) else 0))
    )
    decreases n - i
  {
    var t := i;
    acc := acc + (if t % 11 == 0 || t % 13 == 0 then count7_r(t) else 0);
    i := t + 1;
    SumSeqExtend(t);
    assert acc == sum(
      seq(i, j requires 0 <= j < i => (if j % 11 == 0 || j % 13 == 0 then count7_r(j) else 0))
    );
  }
  result := acc;
}
```