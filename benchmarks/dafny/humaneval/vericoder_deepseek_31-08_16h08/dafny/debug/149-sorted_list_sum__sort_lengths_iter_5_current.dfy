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
method sort_strings(list: seq<string>) returns (sorted: seq<string>)
    ensures |sorted| == |list|
    ensures multiset(sorted) == multiset(list)
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma MultisetPreserved<T>(s: seq<T>)
    ensures multiset(s) == multiset(s[..])
{
}

lemma SortedByLength(a: seq<string>, b: seq<string>)
    requires |a| == |b|
    requires multiset(a) == multiset(b)
    requires forall x : int, y : int :: 0 <= x < y < |a| ==> |a[x]| <= |a[y]|
    requires forall x : int, y : int :: 0 <= x < y < |b| ==> |b[x]| <= |b[y]|
    ensures a == b
{
}

lemma MultisetSwap<T>(s: seq<T>, i: int, j: int)
    requires 0 <= i < j < |s|
    ensures multiset(s[..i] + [s[j]] + s[i+1..j] + [s[i]] + s[j+1..]) == multiset(s)
{
    assert s == s[..i] + [s[i]] + s[i+1..j] + [s[j]] + s[j+1..];
    assert s[..i] + [s[j]] + s[i+1..j] + [s[i]] + s[j+1..] == s[..i] + [s[j]] + s[i+1..j] + [s[i]] + s[j+1..];
}

lemma PermutationPreservesLength<T>(s: seq<T>)
    ensures |s[..]| == |s|
{
}

lemma MultisetSwapPreserves<T>(s: seq<T>, j: int)
    requires 0 <= j-1 < j < |s|
    ensures multiset(s[..j-1] + [s[j]] + [s[j-1]] + s[j+1..]) == multiset(s)
{
    assert s == s[..j-1] + [s[j-1]] + [s[j]] + s[j+1..];
    assert s[..j-1] + [s[j]] + [s[j-1]] + s[j+1..] == s[..j-1] + [s[j]] + [s[j-1]] + s[j+1..];
}

lemma SortedInvariantUpdate(s: seq<string>, i: int, j: int)
    requires 0 <= j-1 < j < |s| && j < i
    requires forall x: int, y: int :: 0 <= x < y < i && (x != j-1 || y != j) ==> |s[x]| <= |s[y]|
    requires |s[j-1]| > |s[j]|
    ensures forall x: int, y: int :: 0 <= x < y < i && (x != j-1 || y != j) ==> |(s[..j-1] + [s[j]] + [s[j-1]] + s[j+1..])[x]| <= |(s[..j-1] + [s[j]] + [s[j-1]] + s[j+1..])[y]|
{
    var swapped := s[..j-1] + [s[j]] + [s[j-1]] + s[j+1..];
    
    // Show that elements at j-1 and j are swapped
    assert forall k: int | 0 <= k < |swapped| && k != j-1 && k != j :: swapped[k] == s[k];
    assert swapped[j-1] == s[j];
    assert swapped[j] == s[j-1];
    assert |swapped[j-1]| == |s[j]|;
    assert |swapped[j]| == |s[j-1]|;
    assert |swapped[j-1]| < |swapped[j]|;
}

lemma IndexInRangeLemma(s: seq<string>, j: int)
    requires 0 <= j < |s|
    ensures j-1 >= 0 ==> j-1 < |s|
{
}
// </vc-helpers>

// <vc-spec>
method sort_lengths(list: seq<string>) returns (sorted: seq<string>)
    requires forall i : int :: 0 <= i < |list| ==> |list[i]| % 2 == 0
    ensures forall i : int :: 0 <= i < |sorted| ==> |sorted[i]| % 2 == 0
    ensures |sorted| == |list|
    ensures multiset(sorted) == multiset(list)
    ensures forall x : int, y : int :: 0 <= x < y < |sorted| ==> |sorted[x]| <= |sorted[y]|
// </vc-spec>
// <vc-code>
{
    sorted := list;
    var i := 1;
    while (i < |sorted|)
        invariant 1 <= i <= |sorted|
        invariant forall x: int, y: int :: 0 <= x < y < i ==> |sorted[x]| <= |sorted[y]|
        invariant multiset(sorted) == multiset(list)
        invariant forall j: int :: 0 <= j < |sorted| ==> |sorted[j]| % 2 == 0
        invariant |sorted| == |list|
    {
        var j := i;
        while (j > 0 && |sorted[j-1]| > |sorted[j]|)
            invariant 0 <= j <= i
            invariant forall x: int, y: int :: 0 <= x < y < i+1 ==> 
                (x != j || y != j+1) ==> |sorted[x]| <= |sorted[y]|
            invariant multiset(sorted) == multiset(list)
            invariant forall k: int :: 0 <= k < |sorted| ==> |sorted[k]| % 2 == 0
            invariant |sorted| == |list|
        {
            IndexInRangeLemma(sorted, j);
            var temp := sorted[j-1];
            sorted := sorted[..j-1] + [sorted[j]] + [temp] + sorted[j+1..];
            j := j - 1;
        }
        i := i + 1;
    }
}
// </vc-code>

method sorted_list_sum(list: seq<string>) returns (sorted: seq<string>)
    requires |list| > 0
    ensures |sorted| <= |list|
    ensures forall i : int :: 0 <= i < |sorted| ==> |sorted[i]| % 2 == 0
    ensures forall x : int, y : int :: 0 <= x < y < |sorted| ==> |sorted[x]| <= |sorted[y]|
    ensures multiset(sorted) <= multiset(list)
{
  assume{:axiom} false;
}