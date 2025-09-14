predicate sorted(s : seq<int>) {
    forall u, w :: 0 <= u < w < |s| ==> s[u] <= s[w]
}

// <vc-helpers>
lemma lemma_min_max(s:seq<int>)
    requires sorted(s)
    requires |s| > 0
    ensures s[0] <= s[|s|-1]
{
}

lemma lemma_split_mid(s:seq<int>, low:int, high:int)
    requires sorted(s)
    requires 0 <= low <= high <= |s|
    ensures sorted(s[low..high])
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
    var low := 0;
    var high := v.Length;
    p := -1;

    while low < high
        invariant 0 <= low <= high <= v.Length
        invariant (forall u::0<=u<low ==> v[u]<=elem)
        invariant (forall w::high<=w<v.Length ==> v[w]>elem)
        invariant -1<=p<v.Length
    {
        var mid := low + (high - low) / 2;
        lemma_split_mid(v[..], low, high);
        lemma_min_max(v[low..high]);
        
        if v[mid] > elem {
            high := mid;
        } else {
            low := mid + 1;
        }
    }
    
    p := low - 1;
    return p;
}
// </vc-code>

//Recursive binary search