predicate sorted(s : seq<int>) {
    forall u, w :: 0 <= u < w < |s| ==> s[u] <= s[w]
}







//Recursive binary search

// <vc-helpers>
lemma MidPointLessThan(v: array<int>, c: int, f: int, mid: int, elem: int)
    requires sorted(v[0..v.Length])
    requires 0 <= c <= mid <= f < v.Length
    requires v[mid] <= elem
    ensures forall k :: c <= k <= mid ==> v[k] <= elem
{
    forall k | c <= k <= mid
        ensures v[k] <= elem
    {
        assert v[k] <= v[mid];
    }
}

lemma MidPointGreaterThan(v: array<int>, c: int, f: int, mid: int, elem: int)
    requires sorted(v[0..v.Length])
    requires 0 <= c <= mid <= f < v.Length
    requires v[mid] > elem
    ensures forall k :: mid <= k <= f ==> v[k] > elem
{
    forall k | mid <= k <= f
        ensures v[k] > elem
    {
        assert v[k] >= v[mid];
    }
}
// </vc-helpers>

// <vc-spec>
method binarySearchRec(v:array<int>, elem:int, c:int, f:int) returns (p:int)
 requires sorted(v[0..v.Length])
 requires 0<=c<=f+1<=v.Length//0<=c<=v.Length && -1<=f<v.Length && c<=f+1
 requires forall k::0<=k<c ==> v[k]<=elem
 requires forall k::f<k<v.Length ==> v[k]>elem
 decreases f-c
 ensures -1<=p<v.Length
 ensures (forall u::0<=u<=p ==> v[u]<=elem) && (forall w::p<w<v.Length ==> v[w]>elem)
// </vc-spec>
// <vc-code>
{
    if c > f {
        return f;
    } else {
        var mid := (c + f) / 2;
        if v[mid] <= elem {
            MidPointLessThan(v, c, f, mid, elem);
            var result := binarySearchRec(v, elem, mid+1, f);
            return result;
        } else {
            MidPointGreaterThan(v, c, f, mid, elem);
            var result := binarySearchRec(v, elem, c, mid-1);
            return result;
        }
    }
}
// </vc-code>

