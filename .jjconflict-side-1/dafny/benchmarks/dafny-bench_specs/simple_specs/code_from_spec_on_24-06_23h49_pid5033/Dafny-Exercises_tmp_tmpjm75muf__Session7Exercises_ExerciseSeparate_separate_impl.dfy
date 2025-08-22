//ATOM

predicate positive(s:seq<int>)
{forall u::0<=u<|s| ==> s[u]>=0}


//ATOM
predicate strictNegative(v:array<int>,i:int,j:int)
reads v
requires 0<=i<=j<=v.Length
{forall u | i<=u<j :: v[u]<0}


//ATOM

predicate isPermutation(s:seq<int>, t:seq<int>)
{multiset(s)==multiset(t)}

/**
returns an index st new array is a permutation of the old array
positive first and then strictnegative, i is the firs neg or len if not any */


//IMPL separate
method separate(v:array<int>) returns (i:int)
modifies v
ensures 0<=i<=v.Length
ensures positive(v[0..i]) && strictNegative(v,i,v.Length)
ensures isPermutation(v[0..v.Length], old(v[0..v.Length]))
{
    if v.Length == 0 {
        return 0;
    }
    
    var left := 0;
    var right := v.Length - 1;
    
    while left <= right
        invariant 0 <= left <= v.Length
        invariant -1 <= right < v.Length
        invariant left <= right + 1
        invariant forall k | 0 <= k < left :: v[k] >= 0
        invariant forall k | right < k < v.Length :: v[k] < 0
        invariant multiset(v[0..v.Length]) == multiset(old(v[0..v.Length]))
    {
        if v[left] >= 0 {
            left := left + 1;
        } else if v[right] < 0 {
            right := right - 1;
        } else {
            // v[left] < 0 and v[right] >= 0, so swap them
            var temp := v[left];
            v[left] := v[right];
            v[right] := temp;
            left := left + 1;
            right := right - 1;
        }
    }
    
    return left;
}