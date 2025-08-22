//IMPL Algorithm 1: From left to right return the first
method mmaximum1(v:array<int>) returns (i:int) 
requires v.Length>0
ensures 0<=i<v.Length 
ensures forall k:: 0<=k<v.Length ==> v[i]>=v[k]
{
    i := 0;
    var j := 1;
    while j < v.Length
        invariant 0 <= i < v.Length
        invariant 1 <= j <= v.Length
        invariant forall k :: 0 <= k < j ==> v[i] >= v[k]
    {
        if v[j] > v[i] {
            i := j;
        }
        j := j + 1;
    }
}

//IMPL Algorithm 2: From right to left return the last
method mmaximum2(v:array<int>) returns (i:int) 
requires v.Length>0
ensures 0<=i<v.Length 
ensures forall k:: 0<=k<v.Length ==> v[i]>=v[k]
{
    i := v.Length - 1;
    var j := v.Length - 2;
    while j >= 0
        invariant -1 <= j < v.Length - 1
        invariant 0 <= i < v.Length
        invariant forall k :: j < k < v.Length ==> v[i] >= v[k]
    {
        if v[j] >= v[i] {
            i := j;
        }
        j := j - 1;
    }
}

//IMPL 
method mfirstMaximum(v:array<int>) returns (i:int)
requires v.Length>0
ensures 0<=i<v.Length 
ensures forall k:: 0<=k<v.Length ==> v[i]>=v[k]
ensures forall l:: 0<=l<i ==> v[i]>v[l]
{
    i := 0;
    var j := 1;
    while j < v.Length
        invariant 0 <= i < v.Length
        invariant 1 <= j <= v.Length
        invariant forall k :: 0 <= k < j ==> v[i] >= v[k]
        invariant forall l :: 0 <= l < i ==> v[i] > v[l]
    {
        if v[j] > v[i] {
            i := j;
        }
        j := j + 1;
    }
}

//IMPL 
method mlastMaximum(v:array<int>) returns (i:int)
requires v.Length>0
ensures 0<=i<v.Length 
ensures forall k:: 0<=k<v.Length ==> v[i]>=v[k]
ensures forall l:: i<l<v.Length ==> v[i]>v[l]
{
    i := v.Length - 1;
    var j := v.Length - 2;
    while j >= 0
        invariant -1 <= j < v.Length - 1
        invariant 0 <= i < v.Length
        invariant forall k :: j < k < v.Length ==> v[i] >= v[k]
        invariant forall l :: i < l < v.Length ==> v[i] > v[l]
    {
        if v[j] > v[i] {
            i := j;
        }
        j := j - 1;
    }
}

//IMPL Algorithm : from left to right
//Algorithm : from right to left
method mmaxvalue1(v:array<int>) returns (m:int)
requires v.Length>0
ensures m in v[..]
ensures forall k::0<=k<v.Length ==> m>=v[k]
{
    m := v[0];
    var i := 1;
    while i < v.Length
        invariant 1 <= i <= v.Length
        invariant m in v[..i]
        invariant forall k :: 0 <= k < i ==> m >= v[k]
    {
        if v[i] > m {
            m := v[i];
        }
        i := i + 1;
    }
}

//IMPL 
method mmaxvalue2(v:array<int>) returns (m:int)
requires v.Length>0
ensures m in v[..]
ensures forall k::0<=k<v.Length ==> m>=v[k]
{
    m := v[v.Length - 1];
    var i := v.Length - 2;
    while i >= 0
        invariant -1 <= i < v.Length - 1
        invariant m in v[i+1..]
        invariant forall k :: i < k < v.Length ==> m >= v[k]
    {
        if v[i] >= m {
            m := v[i];
        }
        i := i - 1;
    }
}