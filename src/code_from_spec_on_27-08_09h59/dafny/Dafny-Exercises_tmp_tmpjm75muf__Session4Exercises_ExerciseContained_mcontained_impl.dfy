predicate strictSorted(s : seq<int>) {
    forall u, w :: 0 <= u < w < |s| ==> s[u] < s[w]
}

// <vc-helpers>
lemma strictSortedSubseq(s: seq<int>, i: int, j: int)
    requires 0 <= i <= j <= |s|
    requires strictSorted(s)
    ensures strictSorted(s[i..j])
{
}

lemma strictSortedImpliesNoDuplicates(s: seq<int>)
    requires strictSorted(s)
    ensures forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
{
}

function binarySearchCorrectness(arr: array<int>, target: int, lo: int, hi: int): bool
    requires strictSorted(arr[..])
    requires 0 <= lo <= hi <= arr.Length
    reads arr
    decreases hi - lo
{
    if lo >= hi then
        false
    else
        var mid := lo + (hi - lo) / 2;
        if arr[mid] == target then
            true
        else if arr[mid] < target then
            binarySearchCorrectness(arr, target, mid + 1, hi)
        else
            binarySearchCorrectness(arr, target, lo, mid)
}

lemma binarySearchCorrectnessLemma(arr: array<int>, target: int, lo: int, hi: int)
    requires strictSorted(arr[..])
    requires 0 <= lo <= hi <= arr.Length
    ensures binarySearchCorrectness(arr, target, lo, hi) <==> target in arr[lo..hi]
    decreases hi - lo
{
    if lo >= hi {
        assert arr[lo..hi] == [];
    } else {
        var mid := lo + (hi - lo) / 2;
        if arr[mid] == target {
            assert target == arr[mid];
            assert lo <= mid < hi;
            assert target in arr[lo..hi];
        } else if arr[mid] < target {
            binarySearchCorrectnessLemma(arr, target, mid + 1, hi);
            if target in arr[lo..hi] {
                if target in arr[lo..mid+1] {
                    strictSortedImpliesNoDuplicates(arr[..]);
                    assert forall k :: lo <= k <= mid ==> arr[k] <= arr[mid] < target;
                    assert false;
                }
            }
        } else {
            binarySearchCorrectnessLemma(arr, target, lo, mid);
            if target in arr[lo..hi] {
                if target in arr[mid..hi] {
                    strictSortedImpliesNoDuplicates(arr[..]);
                    assert forall k :: mid <= k < hi ==> target < arr[mid] <= arr[k];
                    assert false;
                }
            }
        }
    }
}

lemma elementNotFoundInSortedArray(v: array<int>, w: array<int>, i: int, j: int, m: int)
    requires strictSorted(v[..])
    requires strictSorted(w[..])
    requires 0 <= i < v.Length
    requires 0 <= j <= m <= w.Length
    requires j == m || v[i] < w[j]
    requires forall k :: 0 <= k < j ==> w[k] < v[i]
    ensures v[i] !in w[..m]
{
    if v[i] in w[..m] {
        var idx :| 0 <= idx < m && w[idx] == v[i];
        if idx < j {
            assert w[idx] < v[i] && w[idx] == v[i];
            assert false;
        } else if idx >= j && j < m {
            assert v[i] < w[j] && w[j] <= w[idx] == v[i];
            assert false;
        }
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method mcontained(v:array<int>,w:array<int>,n:int,m:int) returns (b:bool)
//Specify and implement an O(m+n) algorithm that returns b
//v and w are strictly increasing ordered arrays
//b is true iff the first n elements of v are contained in the first m elements of w
requires n<=m && n>=0
requires strictSorted(v[..])
requires strictSorted(w[..])
requires v.Length >= n && w.Length >= m
ensures b==forall k:: 0<= k< n ==> v[k] in w[..m]//exists j :: 0 <= j < m && v[k] == w[j]
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    var i := 0;
    var j := 0;
    b := true;
    
    while i < n && j < m && b
        invariant 0 <= i <= n
        invariant 0 <= j <= m
        invariant b ==> forall k :: 0 <= k < i ==> v[k] in w[..m]
        invariant !b ==> exists k :: 0 <= k < i && v[k] !in w[..m]
        invariant b ==> forall k :: 0 <= k < j ==> exists l :: 0 <= l < i && w[k] == v[l]
        invariant b ==> forall k :: 0 <= k < i ==> exists l :: 0 <= l < j && v[k] == w[l]
        decreases if b then (n - i) + (m - j) else 0
    {
        if v[i] == w[j] {
            i := i + 1;
            j := j + 1;
        } else if v[i] < w[j] {
            b := false;
        } else {
            j := j + 1;
        }
    }
    
    if b && i < n {
        elementNotFoundInSortedArray(v, w, i, j, m);
        b := false;
    }
    
    if b {
        assert i == n;
        assert forall k :: 0 <= k < n ==> v[k] in w[..m];
    } else {
        if i < n {
            assert !(forall k :: 0 <= k < n ==> v[k] in w[..m]);
        } else {
            assert exists k :: 0 <= k < n && v[k] !in w[..m];
            assert !(forall k :: 0 <= k < n ==> v[k] in w[..m]);
        }
    }
}
// </vc-code>
