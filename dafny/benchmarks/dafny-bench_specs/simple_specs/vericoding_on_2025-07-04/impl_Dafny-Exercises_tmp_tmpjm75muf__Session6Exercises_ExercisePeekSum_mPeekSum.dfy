//ATOM

predicate isPeek(v:array<int>,i:int)
reads v
requires 0<=i<v.Length
{forall k::0<=k<i ==> v[i]>=v[k]}


//ATOM

function peekSum(v:array<int>,i:int):int
reads v
requires 0<=i<=v.Length
{
if (i==0) then 0
else if isPeek(v,i-1) then v[i-1]+peekSum(v,i-1)
else peekSum(v,i-1)
}

/* code modified by LLM (iteration 1): Added helper function outside method */
function maxUpTo(arr: array<int>, idx: int): int
    reads arr
    requires 0 <= idx < arr.Length
{
    if idx == 0 then arr[0]
    else if arr[idx] > maxUpTo(arr, idx-1) then arr[idx]
    else maxUpTo(arr, idx-1)
}

/* code modified by LLM (iteration 1): Added helper lemma outside method */
lemma MaxUpToProperty(arr: array<int>, idx: int)
    requires 0 <= idx < arr.Length
    ensures forall k :: 0 <= k <= idx ==> maxUpTo(arr, idx) >= arr[k]
    ensures isPeek(arr, idx) <==> arr[idx] == maxUpTo(arr, idx)
{
    if idx == 0 {
        // Base case
    } else {
        MaxUpToProperty(arr, idx-1);
    }
}

/* code modified by LLM (iteration 1): Added lemma to connect peekSum with loop logic */
lemma PeekSumProperty(v: array<int>, i: int, currentSum: int, maxSoFar: int)
    requires 0 < i <= v.Length
    requires maxSoFar == maxUpTo(v, i-1)
    requires currentSum == peekSum(v, i)
    ensures (i < v.Length && v[i] >= maxSoFar) ==> peekSum(v, i+1) == currentSum + v[i]
    ensures (i < v.Length && v[i] < maxSoFar) ==> peekSum(v, i+1) == currentSum
{
    if i < v.Length {
        MaxUpToProperty(v, i);
    }
}

//IMPL

method mPeekSum(v:array<int>) returns (sum:int)
requires v.Length>0
ensures sum==peekSum(v,v.Length)
//Implement and verify an O(v.Length) algorithm to solve this problem
{
    /* code modified by LLM (iteration 1): Initialize with first element as peak */
    sum := v[0];
    var maxSoFar := v[0];
    var i := 1;
    
    while i < v.Length
        invariant 1 <= i <= v.Length
        invariant maxSoFar == maxUpTo(v, i-1)
        invariant sum == peekSum(v, i)
        decreases v.Length - i
    {
        /* code modified by LLM (iteration 1): Added lemma calls to help verification */
        MaxUpToProperty(v, i);
        PeekSumProperty(v, i, sum, maxSoFar);
        
        if v[i] >= maxSoFar {
            sum := sum + v[i];
            maxSoFar := v[i];
        }
        i := i + 1;
    }
}