function comparison(a : string, b : string, i : int): bool
    requires 0 <= i <= |a| && 0 <= i <= |b|
    decreases |a| - i
    decreases |b| - i
    ensures (a == b) ==> comparison(a, b, i)
{
    if (i < |a| && i < |b|) then
        if a[i] < b[i] then
            true
        else if a[i] > b[i] then
            false
        else
            comparison(a, b, i + 1)
    else
        if |a| <= |b| then
            true
        else
            false
}

// <vc-helpers>
lemma ComparisonTransitive(a: string, b: string, c: string)
    ensures comparison(a, b, 0) && comparison(b, c, 0) ==> comparison(a, c, 0)
{
    if comparison(a, b, 0) && comparison(b, c, 0) {
        ComparisonTransitiveHelper(a, b, c, 0);
    }
}

lemma ComparisonTransitiveHelper(a: string, b: string, c: string, i: int)
    requires 0 <= i <= |a| && 0 <= i <= |b| && 0 <= i <= |c|
    requires comparison(a, b, i) && comparison(b, c, i)
    ensures comparison(a, c, i)
    decreases |a| - i, |b| - i, |c| - i
{
    if i < |a| && i < |b| && i < |c| {
        if a[i] < b[i] {
            // a[i] < b[i], and comparison(b, c, i) is true
            // so a[i] < b[i] <= c[i], hence a[i] <= c[i]
            assert a[i] <= c[i];
        } else if a[i] == b[i] {
            if b[i] < c[i] {
                // a[i] == b[i] < c[i]
                assert a[i] < c[i];
            } else if b[i] == c[i] {
                // a[i] == b[i] == c[i], recurse
                ComparisonTransitiveHelper(a, b, c, i + 1);
            }
        }
    }
}

lemma ComparisonReflexive(a: string)
    ensures comparison(a, a, 0)
{
    ComparisonReflexiveHelper(a, 0);
}

lemma ComparisonReflexiveHelper(a: string, i: int)
    requires 0 <= i <= |a|
    ensures comparison(a, a, i)
    decreases |a| - i
{
    if i < |a| {
        ComparisonReflexiveHelper(a, i + 1);
    }
}

lemma ComparisonAntisymmetric(a: string, b: string)
    ensures comparison(a, b, 0) && comparison(b, a, 0) ==> a == b
{
    if comparison(a, b, 0) && comparison(b, a, 0) {
        ComparisonAntisymmetricHelper(a, b, 0);
    }
}

lemma ComparisonAntisymmetricHelper(a: string, b: string, i: int)
    requires 0 <= i <= |a| && 0 <= i <= |b|
    requires comparison(a, b, i) && comparison(b, a, i)
    ensures a[i..] == b[i..]
    decreases |a| - i, |b| - i
{
    if i < |a| && i < |b| {
        assert a[i] == b[i];
        ComparisonAntisymmetricHelper(a, b, i + 1);
    }
}
// </vc-helpers>

// <vc-spec>
method sort_strings(list: seq<string>) returns (sorted: seq<string>)
    ensures |sorted| == |list|
    ensures multiset(sorted) == multiset(list)
// </vc-spec>
// <vc-code>
{
    sorted := list;
    if |sorted| <= 1 {
        return;
    }
    
    var n := |sorted|;
    var i := 0;
    
    while i < n - 1
        invariant 0 <= i <= n - 1
        invariant n == |sorted|
        invariant multiset(sorted) == multiset(list)
        invariant forall j, k :: n - i <= j < k < n ==> comparison(sorted[j], sorted[k], 0)
        invariant forall j, k :: 0 <= j < n - i - 1 && n - i - 1 <= k < n ==> comparison(sorted[j], sorted[k], 0)
    {
        var j := 0;
        while j < n - i - 1
            invariant 0 <= j <= n - i - 1
            invariant n == |sorted|
            invariant multiset(sorted) == multiset(list)
            invariant forall k :: 0 <= k < j ==> comparison(sorted[k], sorted[k + 1], 0)
            invariant forall p, q :: n - i <= p < q < n ==> comparison(sorted[p], sorted[q], 0)
            invariant forall p :: 0 <= p < j && n - i - 1 <= p + 1 < n ==> comparison(sorted[p], sorted[p + 1], 0)
        {
            if !comparison(sorted[j], sorted[j + 1], 0) {
                var temp := sorted[j];
                sorted := sorted[j := sorted[j + 1]][j + 1 := temp];
                
                // Maintain invariants after swap
                assert multiset(sorted) == multiset(old(sorted));
                assert comparison(sorted[j], sorted[j + 1], 0);
            }
            j := j + 1;
        }
        
        // After inner loop, sorted[n-i-1] is in its final position
        assert forall k :: 0 <= k < n - i - 1 ==> comparison(sorted[k], sorted[n - i - 1], 0);
        
        i := i + 1;
    }
}
// </vc-code>

method sort_lengths(list: seq<string>) returns (sorted: seq<string>)
    requires forall i : int :: 0 <= i < |list| ==> |list[i]| % 2 == 0
    ensures forall i : int :: 0 <= i < |sorted| ==> |sorted[i]| % 2 == 0
    ensures |sorted| == |list|
    ensures multiset(sorted) == multiset(list)
    ensures forall x : int, y : int :: 0 <= x < y < |sorted| ==> |sorted[x]| <= |sorted[y]|
{
  assume{:axiom} false;
}
method sorted_list_sum(list: seq<string>) returns (sorted: seq<string>)
    requires |list| > 0
    ensures |sorted| <= |list|
    ensures forall i : int :: 0 <= i < |sorted| ==> |sorted[i]| % 2 == 0
    ensures forall x : int, y : int :: 0 <= x < y < |sorted| ==> |sorted[x]| <= |sorted[y]|
    ensures multiset(sorted) <= multiset(list)
{
  assume{:axiom} false;
}