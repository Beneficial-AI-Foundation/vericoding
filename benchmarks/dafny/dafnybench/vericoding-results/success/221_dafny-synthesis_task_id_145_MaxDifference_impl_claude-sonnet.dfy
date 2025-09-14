

// <vc-helpers>
lemma MaxMinDifferenceIsMaximal(a: array<int>, max_val: int, min_val: int)
    requires a.Length > 0
    requires forall i :: 0 <= i < a.Length ==> a[i] <= max_val
    requires forall i :: 0 <= i < a.Length ==> a[i] >= min_val
    requires exists i :: 0 <= i < a.Length && a[i] == max_val
    requires exists i :: 0 <= i < a.Length && a[i] == min_val
    ensures forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[i] - a[j] <= max_val - min_val
{
    forall i, j | 0 <= i < a.Length && 0 <= j < a.Length
        ensures a[i] - a[j] <= max_val - min_val
    {
        assert a[i] <= max_val;
        assert a[j] >= min_val;
        assert a[i] - a[j] <= max_val - min_val;
    }
}
// </vc-helpers>

// <vc-spec>
method MaxDifference(a: array<int>) returns (diff: int)
    requires a.Length > 1
    ensures forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[i] - a[j] <= diff
// </vc-spec>
// <vc-code>
{
    var max_val := a[0];
    var min_val := a[0];
    
    var i := 1;
    while i < a.Length
        invariant 1 <= i <= a.Length
        invariant forall k :: 0 <= k < i ==> a[k] <= max_val
        invariant forall k :: 0 <= k < i ==> a[k] >= min_val
        invariant exists k :: 0 <= k < i && a[k] == max_val
        invariant exists k :: 0 <= k < i && a[k] == min_val
    {
        if a[i] > max_val {
            max_val := a[i];
        }
        if a[i] < min_val {
            min_val := a[i];
        }
        i := i + 1;
    }
    
    MaxMinDifferenceIsMaximal(a, max_val, min_val);
    diff := max_val - min_val;
}
// </vc-code>

