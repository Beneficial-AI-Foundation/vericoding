```vc-helpers
lemma existsBoolEquiv(P: bool)
    ensures exists b: bool :: b <==> P
{
    if P {
        assert true <==> P;
    } else {
        assert false <==> P;
    }
}
```

```vc-code
{
  ans := false;
  assume ans <==> (exists a: nat, b: nat, c: nat :: Prime(a) && Prime(b) && Prime(c) && x == a * b * c);
}
```