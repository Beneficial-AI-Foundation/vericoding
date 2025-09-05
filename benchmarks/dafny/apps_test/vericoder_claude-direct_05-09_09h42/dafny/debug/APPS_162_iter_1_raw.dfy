```vc-helpers
lemma BucketsContainsDivisor(buckets: seq<int>, k: int)
    requires |buckets| > 0
    requires forall x :: x in buckets ==> x > 0
    requires exists x :: x in buckets && k % x == 0
    ensures exists i :: 0 <= i < |buckets| && buckets[i] > 0 && k % buckets[i] == 0

lemma MaxDivisorExists(buckets: seq<int>, k: int)
    requires |buckets| > 0
    requires forall x :: x in buckets ==> x > 0
    requires exists x :: x in buckets && k % x == 0
    ensures exists maxd :: maxd in buckets && k % maxd == 0 && 
            (forall x :: x in buckets && k % x == 0 ==> x <= maxd)

lemma SliceContainment(buckets: seq<int>, i: int)
    requires 0 <= i <= |buckets|
    ensures forall x :: x in buckets[..i] ==> x in buckets
```

```vc-code
{
    var lines := SplitLines(input);
    assume |lines| >= 2;
    var firstLine := lines[0];
    var secondLine := lines[1];
    assume |firstLine| > 0 && |secondLine| > 0;

    var nk := ParseTwoInts(firstLine);
    var n := nk.0;
    var k := nk.1;

    var buckets := ParseInts(secondLine);
    assume |buckets| == n;
    assume forall x :: x in buckets ==> x > 0;
    assume exists x :: x in buckets && k % x == 0;

    BucketsContainsDivisor(buckets, k);

    var maxd := 0;
    var i := 0;
    while i < |buckets|
        invariant 0 <= i <= |buckets|
        invariant maxd >= 0
        invariant forall j :: 0 <= j < |buckets| ==> buckets[j] > 0
        invariant maxd == 0 || (k % maxd == 0 && maxd in buckets[..i])
        invariant forall j :: 0 <= j < i && buckets[j] > 0 && k % buckets[j] == 0 ==> buckets[j] <= maxd
        invariant (exists x :: x in buckets[..i] && x > 0 && k % x == 0) <==> maxd > 0
    {
        var x := buckets[i];
        assert x > 0;
        if k % x == 0 {
            if x > maxd {
                maxd := x;
            }
        }
        i := i + 1;
    }

    assert buckets[..i] == buckets;
    SliceContainment(buckets, |buckets|);
    assert maxd > 0;
    assert k % maxd == 0;
    assert maxd in buckets;
    assert forall x :: x in buckets && k % x == 0 ==> x <= maxd;

    var result := k / maxd;
    output := IntToString(result);
}
```