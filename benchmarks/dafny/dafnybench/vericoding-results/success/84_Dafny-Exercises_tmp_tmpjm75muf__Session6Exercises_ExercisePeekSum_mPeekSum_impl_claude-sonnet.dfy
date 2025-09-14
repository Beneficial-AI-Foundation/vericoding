predicate isPeek(v:array<int>,i:int)
 reads v
 requires 0<=i<v.Length
 {forall k::0<=k<i ==> v[i]>=v[k]}

 function peekSum(v:array<int>,i:int):int
 decreases i 
 reads v
 requires 0<=i<=v.Length
 {
  if (i==0) then 0
  else if isPeek(v,i-1) then v[i-1]+peekSum(v,i-1)
  else peekSum(v,i-1)
 }

// <vc-helpers>
function maxUpTo(v: array<int>, i: int): int
    reads v
    requires 0 < i <= v.Length
{
    if i == 1 then v[0]
    else if v[i-1] >= maxUpTo(v, i-1) then v[i-1]
    else maxUpTo(v, i-1)
}

lemma maxUpToProperty(v: array<int>, i: int)
    requires 0 < i <= v.Length
    ensures forall k :: 0 <= k < i ==> v[k] <= maxUpTo(v, i)
    ensures exists k :: 0 <= k < i && v[k] == maxUpTo(v, i)
{
    if i == 1 {
        // Base case
    } else {
        maxUpToProperty(v, i-1);
    }
}

lemma isPeekEquivalence(v: array<int>, i: int, maxVal: int)
    requires 0 <= i < v.Length
    requires i == 0 ==> maxVal == v[0]
    requires i > 0 ==> (forall k :: 0 <= k < i ==> v[k] <= maxVal)
    requires i > 0 ==> (exists k :: 0 <= k < i && v[k] == maxVal)
    ensures isPeek(v, i) <==> v[i] >= maxVal
{
    if i == 0 {
        // Base case: isPeek(v, 0) is always true (forall k::0<=k<0 is vacuously true)
        // and maxVal == v[0], so v[0] >= maxVal is v[0] >= v[0] which is true
        assert isPeek(v, 0);
        assert v[0] >= v[0];
    } else {
        // For i > 0, isPeek(v, i) means v[i] >= v[k] for all k in [0, i)
        // Since maxVal is the maximum of v[0..i), this is equivalent to v[i] >= maxVal
    }
}
// </vc-helpers>

// <vc-spec>
method mPeekSum(v:array<int>) returns (sum:int)
 requires  v.Length>0
 ensures sum==peekSum(v,v.Length)
 //Implement and verify an O(v.Length) algorithm to solve this problem
// </vc-spec>
// <vc-code>
{
    sum := 0;
    var i := 0;
    var maxVal := v[0];
    
    while i < v.Length
        invariant 0 <= i <= v.Length
        invariant sum == peekSum(v, i)
        invariant i > 0 ==> (forall k :: 0 <= k < i ==> v[k] <= maxVal)
        invariant i > 0 ==> (exists k :: 0 <= k < i && v[k] == maxVal)
        invariant i == 0 ==> maxVal == v[0]
    {
        if i == 0 || v[i] >= maxVal {
            isPeekEquivalence(v, i, maxVal);
            sum := sum + v[i];
        } else {
            isPeekEquivalence(v, i, maxVal);
        }
        
        if i == 0 || v[i] >= maxVal {
            maxVal := v[i];
        }
        
        i := i + 1;
    }
}
// </vc-code>

