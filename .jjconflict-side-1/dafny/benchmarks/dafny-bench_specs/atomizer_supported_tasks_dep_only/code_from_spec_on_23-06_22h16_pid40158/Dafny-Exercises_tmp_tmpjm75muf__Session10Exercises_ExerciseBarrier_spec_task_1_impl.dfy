//IMPL barrier method
method barrier(v:array<int>,p:int) returns (b:bool)
requires v.Length > 0
requires 0<=p<v.Length
ensures b == (forall k,l::0<=k<=p && p<l<v.Length ==> v[k]<v[l])
{
    // Find the maximum element in the left part (positions 0 to p)
    var i := 1;
    var max := 0;
    
    while i <= p
        invariant 1 <= i <= p + 1
        invariant 0 <= max <= p
        invariant forall j :: 0 <= j < i && j <= p ==> v[j] <= v[max]
    {
        if v[i] > v[max] {
            max := i;
        }
        i := i + 1;
    }
    
    // Check if all elements in the right part are greater than the maximum of the left part
    i := p + 1;
    while i < v.Length && v[i] > v[max]
        invariant p + 1 <= i <= v.Length
        invariant forall j :: p + 1 <= j < i ==> v[j] > v[max]
    {
        i := i + 1;
    }
    
    b := (i == v.Length);
}