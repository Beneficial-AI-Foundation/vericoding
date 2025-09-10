function min(a: seq<int>): int
    requires |a| > 0
    ensures min(a) in a
    ensures forall i :: 0 <= i < |a| ==> min(a) <= a[i]
{
    if |a| == 1 then a[0]
    else if a[0] <= min(a[1..]) then a[0]
    else min(a[1..])
}

// <vc-helpers>
lemma MinDividesAll(a: seq<int>)
    requires |a| > 0
    requires forall i :: 0 <= i < |a| ==> a[i] > 0
    requires forall i :: 0 <= i < |a| ==> a[i] % min(a) == 0
    ensures forall x :: x in a ==> forall i :: 0 <= i < |a| ==> a[i] % x == 0
{
    var minVal := min(a);
    forall x | x in a
        ensures forall i :: 0 <= i < |a| ==> a[i] % x == 0
    {
        assert x % minVal == 0;
        forall i | 0 <= i < |a|
            ensures a[i] % x == 0
        {
            assert a[i] % minVal == 0;
            DivisibilityTransitive(x, minVal, a[i]);
        }
    }
}

lemma DivisibilityTransitive(x: int, minVal: int, ai: int)
    requires x > 0 && minVal > 0 && ai > 0
    requires x % minVal == 0
    requires ai % minVal == 0
    ensures ai % x == 0
{
    var k1 := x / minVal;
    var k2 := ai / minVal;
    assert x == k1 * minVal;
    assert ai == k2 * minVal;
    
    var k3 := k2 / k1;
    var r := k2 % k1;
    assert k2 == k3 * k1 + r;
    assert 0 <= r < k1;
    
    calc {
        ai;
        == k2 * minVal;
        == (k3 * k1 + r) * minVal;
        == k3 * k1 * minVal + r * minVal;
        == k3 * x + r * minVal;
    }
    
    if r == 0 {
        assert ai == k3 * x;
        assert ai % x == 0;
    } else {
        assert ai == k3 * x + r * minVal;
        assert r > 0;
        assert r * minVal > 0;
        assert ai > k3 * x;
        assert (ai - k3 * x) % x == (r * minVal) % x;
        
        var q := r * minVal / x;
        var rem := r * minVal % x;
        assert r * minVal == q * x + rem;
        assert 0 <= rem < x;
        
        if rem == 0 {
            assert r * minVal % x == 0;
            assert ai % x == 0;
        } else {
            assert rem > 0;
            assert rem < x;
            assert rem < k1 * minVal;
            assert rem % minVal < minVal;
            assert rem < minVal;
            assert false;
        }
    }
}

lemma GCDProperty(x: int, minVal: int)
    requires x > 0 && minVal > 0
    requires minVal <= x
    requires x % minVal == 0
    ensures forall ai :: ai > 0 && ai % minVal == 0 ==> ai % x == 0
{
    forall ai | ai > 0 && ai % minVal == 0
        ensures ai % x == 0
    {
        DivisibilityTransitive(x, minVal, ai);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(a: seq<int>) returns (result: int)
    requires |a| > 0
    requires forall i :: 0 <= i < |a| ==> a[i] > 0
    ensures result == -1 || result in a
    ensures result != -1 ==> forall i :: 0 <= i < |a| ==> a[i] % result == 0
    ensures result == -1 ==> forall x :: x in a ==> exists i :: 0 <= i < |a| && a[i] % x != 0
    ensures (forall i :: 0 <= i < |a| ==> a[i] % (min(a)) == 0) ==> result == min(a)
    ensures (exists i :: 0 <= i < |a| && a[i] % (min(a)) != 0) ==> result == -1
// </vc-spec>
// <vc-code>
{
    var minVal := min(a);
    var allDivisible := true;
    
    var i := 0;
    while i < |a|
        invariant 0 <= i <= |a|
        invariant allDivisible ==> forall j :: 0 <= j < i ==> a[j] % minVal == 0
        invariant !allDivisible ==> exists j :: 0 <= j < i && a[j] % minVal != 0
    {
        if a[i] % minVal != 0 {
            allDivisible := false;
        }
        i := i + 1;
    }
    
    if allDivisible {
        assert forall j :: 0 <= j < |a| ==> a[j] % minVal == 0;
        MinDividesAll(a);
        result := minVal;
    } else {
        assert exists j :: 0 <= j < |a| && a[j] % minVal != 0;
        result := -1;
    }
}
// </vc-code>

