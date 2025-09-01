

// <vc-helpers>
lemma lemma_max_property(l: seq<int>, i: int, max: int)
    requires 0 <= i < |l|
    requires max == l[i]
    requires forall j: int :: 0 <= j < i ==> l[j] <= max
    requires forall k: int :: 0 <= k < |l| ==> l[k] <= max || exists m: int :: 0 <= m < i && l[m] > l[k]
    ensures forall k: int :: 0 <= k < |l| ==> l[k] <= max
{
    forall k: int | 0 <= k < |l|
        ensures l[k] <= max
    {
        if l[k] > max {
            assert exists m: int :: 0 <= m < i && l[m] > l[k];
            var m :| 0 <= m < i && l[m] > l[k];
            assert l[m] <= max;
            assert l[k] < l[m] <= max;
        }
    }
}
// </vc-helpers>

// <vc-spec>
method max_element(l : seq<int>) returns (result : int)
    // pre-conditions-start
    requires |l| > 0
    // pre-conditions-end
    // post-conditions-start
    ensures forall i : int :: i >= 0 && i < |l| ==> l[i] <= result
    ensures exists i : int :: i >= 0 && i < |l| && l[i] == result
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    var max := l[0];
    var i := 0;

    while i < |l|
        invariant 0 <= i <= |l|
        invariant forall j : int :: 0 <= j < i ==> l[j] <= max
        invariant max in l[..i]
    {
        if l[i] > max {
            max := l[i];
        }
        i := i + 1;
    }

    return max;
}
// </vc-code>

