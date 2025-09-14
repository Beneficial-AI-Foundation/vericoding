predicate sorted(s : seq<int>) {
    forall u, w :: 0 <= u < w < |s| ==> s[u] <= s[w]
}

method binarySearch(v:array<int>, elem:int) returns (p:int)
 requires sorted(v[0..v.Length])
 ensures -1<=p<v.Length
 ensures (forall u::0<=u<=p ==> v[u]<=elem) && (forall w::p<w<v.Length ==> v[w]>elem)
{
  assume{:axiom} false;
}






//Recursive binary search

// <vc-helpers>
method BinarySearchRec(v: array<int>, elem: int, low: int, high: int) returns (b: bool, p: int)
    requires 0 <= low <= high < v.Length
    requires sorted(v[low..high+1])
    ensures low <= p <= high+1
    ensures b == (elem in v[low..high+1])
    ensures b ==> low <= p <= high && v[p] == elem
    ensures !b ==> ( (forall u :: low <= u < p ==> v[u] < elem) && (forall w :: p <= w <= high ==> v[w] > elem) )
{
    if low > high {
        return (false, low);
    }
    var mid := (low + high) / 2;
    if v[mid] == elem {
        return (true, mid);
    } else if v[mid] < elem {
        assert forall u :: low <= u <= mid ==> v[u] <= v[mid];
        assert v[mid] < elem;
        assert forall u :: low <= u <= mid ==> v[u] < elem;
        var (b_found, p_found) := BinarySearchRec(v, elem, mid+1, high);
        return (b_found, p_found);
    } else {
        assert forall w :: mid <= w <= high ==> v[w] >= v[mid];
        assert v[mid] > elem;
        assert forall w :: mid <= w <= high ==> v[w] > elem;
        var (b_found, p_found) := BinarySearchRec(v, elem, low, mid-1);
        return (b_found, p_found);
    }
}
// </vc-helpers>

// <vc-spec>
method otherbSearch(v:array<int>, elem:int) returns (b:bool,p:int)
 requires sorted(v[0..v.Length])
 ensures 0<=p<=v.Length
 ensures b == (elem in v[0..v.Length])
 ensures b ==> p<v.Length && v[p]==elem
 ensures !b ==> (forall u::0<=u<p ==> v[u]<elem) && 
               (forall w::p<=w<v.Length ==> v[w]>elem)
 //Implement and verify
// </vc-spec>
// <vc-code>
{
    if v.Length == 0 {
        return (false, 0);
    }
    var (b_found, p_found) := BinarySearchRec(v, elem, 0, v.Length-1);
    return (b_found, p_found);
}
// </vc-code>

