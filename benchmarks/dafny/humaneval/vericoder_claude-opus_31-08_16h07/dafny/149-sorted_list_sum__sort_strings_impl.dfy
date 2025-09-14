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
            assert b[i] <= c[i];
            assert a[i] < c[i];
        } else if a[i] == b[i] {
            if b[i] < c[i] {
                assert a[i] < c[i];
            } else if b[i] == c[i] {
                ComparisonTransitiveHelper(a, b, c, i + 1);
            }
        }
    } else if i >= |a| || i >= |b| || i >= |c| {
        if i >= |a| && i < |b| && i < |c| {
            assert comparison(a, b, i);
            assert |a| <= |b|;
            if b[i] < c[i] {
                assert comparison(a, c, i);
            } else if b[i] == c[i] {
                ComparisonTransitiveHelper(a, b, c, i + 1);
            }
        } else if i >= |a| && i >= |b| {
            assert |a| <= |b| && |b| <= |c|;
            assert |a| <= |c|;
        } else if i >= |a| && i >= |c| {
            assert |a| <= |b|;
            assert |b| <= |c|;
            assert |a| <= |c|;
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
        assert a[i] == a[i];
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
        assert a[i] <= b[i] && b[i] <= a[i];
        assert a[i] == b[i];
        ComparisonAntisymmetricHelper(a, b, i + 1);
    } else {
        assert |a| - i == |b| - i;
    }
}

lemma SwapMaintainsSortedSuffix(sorted: seq<string>, j: int, n: int, i: int)
    requires 0 <= j < j + 1 < n == |sorted|
    requires 0 <= i < n
    requires forall p, q :: n - i <= p < q < n ==> comparison(sorted[p], sorted[q], 0)
    requires !comparison(sorted[j], sorted[j + 1], 0)
    ensures var sorted' := sorted[j := sorted[j + 1]][j + 1 := sorted[j]];
            forall p, q :: n - i <= p < q < n ==> comparison(sorted'[p], sorted'[q], 0)
{
    var sorted' := sorted[j := sorted[j + 1]][j + 1 := sorted[j]];
    forall p, q | n - i <= p < q < n
        ensures comparison(sorted'[p], sorted'[q], 0)
    {
        if p == j && q == j + 1 {
            assert sorted'[p] == sorted[j + 1];
            assert sorted'[q] == sorted[j];
            assert !comparison(sorted[j], sorted[j + 1], 0);
            assert comparison(sorted[j + 1], sorted[j], 0);
            assert comparison(sorted'[p], sorted'[q], 0);
        } else if p == j {
            assert sorted'[p] == sorted[j + 1];
            assert sorted'[q] == sorted[q];
            assert comparison(sorted[n - i], sorted[q], 0) by {
                if n - i == j + 1 {
                    assert sorted[n - i] == sorted[j + 1];
                } else if n - i < j + 1 {
                    assert comparison(sorted[n - i], sorted[j + 1], 0);
                    ComparisonTransitive(sorted[n - i], sorted[j + 1], sorted[q]);
                }
            }
        } else if q == j + 1 {
            assert sorted'[p] == sorted[p];
            assert sorted'[q] == sorted[j];
        } else {
            assert sorted'[p] == sorted[p];
            assert sorted'[q] == sorted[q];
            assert comparison(sorted[p], sorted[q], 0);
        }
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
        invariant forall p, q :: n - i <= p < q < n ==> comparison(sorted[p], sorted[q], 0)
        invariant forall p, q :: 0 <= p < n - i && n - i <= q < n ==> comparison(sorted[p], sorted[q], 0)
    {
        var j := 0;
        while j < n - i - 1
            invariant 0 <= j <= n - i - 1
            invariant n == |sorted|
            invariant multiset(sorted) == multiset(list)
            invariant forall k :: 0 <= k < j ==> comparison(sorted[k], sorted[k + 1], 0)
            invariant forall k :: 0 <= k <= j < n ==> comparison(sorted[k], sorted[j], 0)
            invariant forall p, q :: n - i <= p < q < n ==> comparison(sorted[p], sorted[q], 0)
            invariant forall p, q :: 0 <= p < n - i && n - i <= q < n ==> comparison(sorted[p], sorted[q], 0)
        {
            if !comparison(sorted[j], sorted[j + 1], 0) {
                var temp := sorted[j];
                var old_sorted := sorted;
                sorted := sorted[j := sorted[j + 1]][j + 1 := temp];
                
                assert multiset(sorted) == multiset(old_sorted);
                assert comparison(sorted[j], sorted[j + 1], 0);
                
                SwapMaintainsSortedSuffix(old_sorted, j, n, i);
                
                forall k | 0 <= k < j
                    ensures comparison(sorted[k], sorted[k + 1], 0)
                {
                    if k + 1 == j {
                        assert sorted[k] == old_sorted[k];
                        assert sorted[k + 1] == old_sorted[j + 1];
                        assert comparison(old_sorted[k], old_sorted[j], 0);
                        assert !comparison(old_sorted[j], old_sorted[j + 1], 0);
                        assert comparison(old_sorted[j + 1], old_sorted[j], 0);
                        ComparisonTransitive(old_sorted[k], old_sorted[j + 1], old_sorted[j]);
                        assert comparison(sorted[k], sorted[k + 1], 0);
                    } else {
                        assert sorted[k] == old_sorted[k];
                        assert sorted[k + 1] == old_sorted[k + 1];
                    }
                }
                
                forall k | 0 <= k <= j < n
                    ensures comparison(sorted[k], sorted[j], 0)
                {
                    if k == j {
                        ComparisonReflexive(sorted[j]);
                    } else if k < j {
                        assert sorted[k] == old_sorted[k];
                        assert sorted[j] == old_sorted[j + 1];
                        assert comparison(old_sorted[k], old_sorted[j], 0);
                        assert !comparison(old_sorted[j], old_sorted[j + 1], 0);
                        assert comparison(old_sorted[j + 1], old_sorted[j], 0);
                        ComparisonTransitive(old_sorted[k], old_sorted[j + 1], old_sorted[j]);
                        assert comparison(sorted[k], sorted[j], 0);
                    }
                }
            }
            j := j + 1;
        }
        
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