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


//IMPL

method mPeekSum(v:array<int>) returns (sum:int)
requires v.Length>0
ensures sum==peekSum(v,v.Length)
//Implement and verify an O(v.Length) algorithm to solve this problem
{
    /* code modified by LLM (iteration 1): Fixed compilation errors and implemented correct algorithm */
    sum := v[0];
    var maxSoFar := v[0];
    var i := 1;
    
    while i < v.Length
        invariant 1 <= i <= v.Length
        invariant maxSoFar >= v[0]
        invariant sum == peekSum(v, i)
        invariant forall k :: 0 <= k < i ==> v[k] <= maxSoFar
        invariant exists k :: 0 <= k < i && v[k] == maxSoFar
    {
        if v[i] >= maxSoFar {
            sum := sum + v[i];
            maxSoFar := v[i];
        }
        i := i + 1;
    }
}