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
function gcd(a: int, b: int): int
    requires a >= 0 && b >= 0
    ensures gcd(a, b) >= 0
    ensures (a == 0 && b == 0) ==> gcd(a, b) == 0
    ensures (a == 0 && b != 0) ==> gcd(a, b) == b
    ensures (a != 0 && b == 0) ==> gcd(a, b) == a
    ensures a > 0 && b > 0 ==> a % gcd(a,b) == 0 && b % gcd(a,b) == 0
    ensures a > 0 && b > 0 ==> forall d :: d > 0 && a % d == 0 && b % d == 0 ==> d <= gcd(a,b)
{
    if a == 0 then b
    else if b == 0 then a
    else if a > b then gcd(a % b, b)
    else gcd(a, b % a)
}

function array_gcd(a: seq<int>): int
    requires |a| > 0
    requires forall i :: 0 <= i < |a| ==> a[i] > 0
    ensures array_gcd(a) > 0
    ensures forall i :: 0 <= i < |a| ==> a[i] % array_gcd(a) == 0
    ensures forall d :: d > 0 && (forall i :: 0 <= i < |a| ==> a[i] % d == 0) ==> d <= array_gcd(a)
{
    if |a| == 1 then a[0]
    else gcd(a[0], array_gcd(a[1..]))
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
    var currentGcd := a[0];
    var minValue := a[0];

    for i := 1 to |a| - 1
        invariant 0 <= i <= |a|
        invariant currentGcd == array_gcd(a[0..i])
        invariant minValue == min(a[0..i])
    {
        currentGcd := gcd(currentGcd, a[i]);
        if a[i] < minValue {
            minValue := a[i];
        }
    }

    if (forall k :: 0 <= k < |a| ==> a[k] % minValue == 0) then
        result := minValue;
    else
        result := -1;
}
// </vc-code>

