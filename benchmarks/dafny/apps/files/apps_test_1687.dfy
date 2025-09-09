Given an array of positive integers, find an element from the array such that all elements
in the array are divisible by it. If no such element exists, return -1. If multiple valid
elements exist, return any one of them.

function min(a: seq<int>): int
    requires |a| > 0
    ensures min(a) in a
    ensures forall i :: 0 <= i < |a| ==> min(a) <= a[i]
{
    if |a| == 1 then a[0]
    else if a[0] <= min(a[1..]) then a[0]
    else min(a[1..])
}

method solve(a: seq<int>) returns (result: int)
    requires |a| > 0
    requires forall i :: 0 <= i < |a| ==> a[i] > 0
    ensures result == -1 || result in a
    ensures result != -1 ==> forall i :: 0 <= i < |a| ==> a[i] % result == 0
    ensures result == -1 ==> forall x :: x in a ==> exists i :: 0 <= i < |a| && a[i] % x != 0
    ensures (forall i :: 0 <= i < |a| ==> a[i] % (min(a)) == 0) ==> result == min(a)
    ensures (exists i :: 0 <= i < |a| && a[i] % (min(a)) != 0) ==> result == -1
{
    var minVal := a[0];

    // Find minimum element
    for i := 1 to |a|
        invariant 0 <= i <= |a|
        invariant minVal > 0
        invariant minVal in a
        invariant forall j :: 0 <= j < i ==> minVal <= a[j]
    {
        if a[i] < minVal {
            minVal := a[i];
        }
    }

    // Check if all elements are divisible by minimum
    for i := 0 to |a|
        invariant 0 <= i <= |a|
        invariant minVal in a
        invariant minVal > 0
        invariant forall j :: 0 <= j < |a| ==> minVal <= a[j]
        invariant forall j :: 0 <= j < i ==> a[j] % minVal == 0
    {
        if a[i] % minVal != 0 {
            // Prove that no element in a can divide all elements
            assert exists k :: 0 <= k < |a| && a[k] % minVal != 0;
            assert forall x :: x in a ==> (x >= minVal && (exists k :: 0 <= k < |a| && a[k] % x != 0));
            result := -1;
            return;
        }
    }

    result := minVal;
}
