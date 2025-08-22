//IMPL barrier
method barrier(v:array<int>,p:int) returns (b:bool)
requires v.Length > 0
requires 0<=p<v.Length
ensures b==forall k,l::0<=k<=p && p<l<v.Length ==> v[k]<v[l]
{
    if p == v.Length - 1 {
        // If p is the last index, there are no elements to the right
        b := true;
        return;
    }
    
    // Find maximum in left partition [0..p]
    var i := 0;
    var maxLeft := v[0];
    while i <= p
        invariant 0 <= i <= p + 1
        invariant maxLeft == v[0] || exists j :: 0 <= j < i && v[j] == maxLeft
        invariant forall j :: 0 <= j < i ==> v[j] <= maxLeft
    {
        if v[i] > maxLeft {
            maxLeft := v[i];
        }
        i := i + 1;
    }
    
    // Find minimum in right partition [p+1..Length-1]
    i := p + 1;
    var minRight := v[p + 1];
    while i < v.Length
        invariant p + 1 <= i <= v.Length
        invariant minRight == v[p + 1] || exists j :: p + 1 <= j < i && v[j] == minRight
        invariant forall j :: p + 1 <= j < i ==> minRight <= v[j]
    {
        if v[i] < minRight {
            minRight := v[i];
        }
        i := i + 1;
    }
    
    // The barrier property holds iff maxLeft < minRight
    b := maxLeft < minRight;
}