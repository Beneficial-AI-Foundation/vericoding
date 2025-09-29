predicate sorted(s : seq<int>) {
    forall u, w :: 0 <= u < w < |s| ==> s[u] <= s[w]
}

// <vc-helpers>
lemma SortedSubsequence(s: seq<int>, lo: int, hi: int)
    requires sorted(s)
    requires 0 <= lo <= hi <= |s|
    ensures sorted(s[lo..hi])
{
    assert forall u, w :: 0 <= u < w < |s[lo..hi]| ==> s[lo..hi][u] <= s[lo..hi][w] by {
        forall u, w | 0 <= u < w < |s[lo..hi]| 
            ensures s[lo..hi][u] <= s[lo..hi][w]
        {
            assert s[lo..hi][u] == s[lo + u];
            assert s[lo..hi][w] == s[lo + w];
            assert 0 <= lo + u < lo + w < |s|;
        }
    }
}

lemma SortedImpliesOrdered(s: seq<int>, i: int, j: int)
    requires sorted(s)
    requires 0 <= i < j < |s|
    ensures s[i] <= s[j]
{
}
// </vc-helpers>

// <vc-spec>
method binarySearch(v:array<int>, elem:int) returns (p:int)
 requires sorted(v[0..v.Length])
 ensures -1<=p<v.Length
 ensures (forall u::0<=u<=p ==> v[u]<=elem) && (forall w::p<w<v.Length ==> v[w]>elem)
// </vc-spec>
// <vc-code>
{
    var lo := 0;
    var hi := v.Length;
    
    while lo < hi
        invariant 0 <= lo <= hi <= v.Length
        invariant forall u :: 0 <= u < lo ==> v[u] <= elem
        invariant forall w :: hi <= w < v.Length ==> v[w] > elem
    {
        var mid := (lo + hi) / 2;
        
        if v[mid] <= elem {
            lo := mid + 1;
        } else {
            hi := mid;
        }
    }
    
    p := lo - 1;
}
// </vc-code>

//Recursive binary search