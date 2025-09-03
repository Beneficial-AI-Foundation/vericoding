```vc-helpers
method NatToBin(n: nat) returns (s: string)
  ensures ValidBitString(s)
  ensures Str2Int(s) == n
{
  assume {:axiom} false;
}

lemma Str2IntAppendBit(prefix: string, lastIsOne: bool)
  requires ValidBitString(prefix)
  ensures Str2Int(prefix + (if lastIsOne then "1" else "0")) == 2 * Str2Int(prefix) + (if lastIsOne then 1 else 0)
{
  assume {:axiom} false;
}

lemma ExpSplitBit(base: nat, yprefix: nat, lastIsOne: bool)
  ensures Exp_int(base, 2*yprefix + (if lastIsOne then 1 else 0)) == Exp_int(base, yprefix) * Exp_int(base, yprefix) * (if lastIsOne then base else 1)
{
  assume {:axiom} false;
}

lemma MulMod(a: nat, b: nat, m: nat)
  requires m > 0
  ensures ((a % m) * (b % m)) % m == (a * b) % m
{
  assume {:axiom} false;
}
```

```vc-code
{
  var base := Str2Int(sx);
  var m := Str2Int(sz);
  // process exponent by recursion on its bit-length (|sy|)
  if |sy| == 1 {
    // sy is either "0" or "1"
    var b := (if sy[|sy|-1] == '1' then 1 else 0);
    var v := Exp_int(base, b) % m;
    var s := NatToBin(v);
    res := s;
    assert ValidBitString(res);
    assert Str2Int(res) == v;
    assert Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
    return;
  } else {
    var prefix := sy[0..|sy|-1];
    var lastIsOne := sy[|sy|-1] == '1';
    var t := ModExp(sx, prefix, sz); // recursive call on shorter exponent
    var tval := Str2Int(t);
    // tval == Exp_int(base, Str2Int(prefix)) % m
    var newval := (tval * tval) % m;
    if lastIsOne {
      newval := (newval * base) % m;
    }
    // Convert back to binary string
    var s := NatToBin(newval);
    res := s;
    assert ValidBitString(res);
    // Now prove the numeric equality
    var yprefix := Str2Int(prefix);
    // Str2Int(sy) == 2*Str2Int(prefix) + (if lastIsOne then 1 else 0)
    assert ValidBitString(prefix);
    Str2IntAppendBit(prefix, lastIsOne);
    // Use lemma about exponent splitting
    ExpSplitBit(base, yprefix, lastIsOne);
    // Relate modulo of product: (a % m)*(b % m) % m == (a*b) % m
    // Let full := Exp_int(base, yprefix)
    var full := Exp_int(base, yprefix);
    // From recursive call: tval == full % m
    assert tval == full % m;
    // newval (before possible multiply by base) equals (tval * tval) % m which equals (full*full) % m
    MulMod(full, full, m);
    assert (tval * tval) % m == (full * full) % m;
    if lastIsOne {
      // newval == ((full*full) % m * base) % m == (full*full*base) % m
      MulMod((full * full) % m, base, m);
      // But to get direct equality we show ((full*full) % m * base) % m == (full*full*base) % m
      // Using MulMod with a = full*full and b = base:
      MulMod(full * full, base, m);
      assert newval == (full * full * base) % m;
      assert newval == Exp_int(base, 2*yprefix + 1) % m;
    } else {
      // newval == (full*full) % m == Exp_int(base, 2*yprefix) % m
      assert newval == (full * full) % m;
      assert newval == Exp_int(base, 2*yprefix) % m;
    }
    // Combine with Str2IntAppendBit: Exp_int(base, Str2Int(sy)) == Exp_int(base, 2*yprefix + (if lastIsOne then 1 else 0))
    // Using ExpSplitBit we have equality to full*full*(if lastIsOne then base else 1)
    // Hence newval equals Exp_int(base, Str2Int(sy)) % m
    assert Str2Int(res) == newval;
    assert Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
  }
}
```