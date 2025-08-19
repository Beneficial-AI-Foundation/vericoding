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
    i := 0;
    var j := v.Length - 1;
    
    while i <= j
        invariant 0 <= i <= v.Length
        invariant -1 <= j < v.Length
        invariant i <= j + 1
        invariant forall k :: 0 <= k < i ==> v[k] >= 0
        invariant forall k :: j < k < v.Length ==> v[k] < 0
        invariant multiset(v[0..v.Length]) == multiset(old(v[0..v.Length]))
    {
        if v[i] >= 0 {
            i := i + 1;
        } else if v[j] < 0 {
            j := j - 1;
        } else {
            // v[i] < 0 and v[j] >= 0, so swap them
            var temp := v[i];
            v[i] := v[j];
            v[j] := temp;
            i := i + 1;
            j := j - 1;
        }
    }
}