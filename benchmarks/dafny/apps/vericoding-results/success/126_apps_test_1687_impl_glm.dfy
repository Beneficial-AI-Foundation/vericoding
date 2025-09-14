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
lemma MinAndDivisor(a: seq<int>, m: int, k: int)
    requires |a| > 0
    requires forall i :: 0 <= i < |a| ==> a[i] > 0
    requires m == min(a)
    requires 0 <= k < |a|
    requires a[k] % m != 0
    ensures forall x :: x in a ==> exists i :: 0<=i<|a| && a[i] % x != 0
{
    forall x | x in a
        ensures exists i :: 0<=i<|a| && a[i] % x != 0
    {
        if x == m {
            assert a[k] % x != 0;
        } else {
            assert m < x;
            assert m % x == m;
            assert m % x != 0;
        }
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
    var m := min(a);
    for i := 0 to |a|
        invariant 0 <= i <= |a|
        invariant forall j :: 0 <= j < i ==> a[j] % m == 0
    {
        if a[i] % m != 0 {
            MinAndDivisor(a, m, i);
            return -1;
        }
    }
    return m;
}
// </vc-code>

