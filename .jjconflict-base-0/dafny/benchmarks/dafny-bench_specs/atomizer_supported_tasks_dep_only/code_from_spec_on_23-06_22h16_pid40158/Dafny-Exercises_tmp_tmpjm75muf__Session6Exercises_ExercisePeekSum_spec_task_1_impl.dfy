// ATOM 

 predicate isPeek(v:array<int>,i:int)
 reads v
 requires 0<=i<v.Length
 {forall k::0<=k<i ==> v[i]>=v[k]}


// ATOM 

 function peekSum(v:array<int>,i:int):int
 reads v
 requires 0<=i<=v.Length
 {
  if (i==0) then 0
  else if isPeek(v,i-1) then v[i-1]+peekSum(v,i-1)
  else peekSum(v,i-1)
 }


// IMPL 

 method mPeekSum(v:array<int>) returns (sum:int)
 requires  v.Length>0
 ensures sum==peekSum(v,v.Length)
 //Implement and verify an O(v.Length) algorithm to solve this problem
 {
    /* code modified by LLM (iteration 1): Initialize sum and tracking variables */
    sum := 0;
    var maxSoFar := v[0];
    var i := 0;
    
    /* code modified by LLM (iteration 1): Fixed loop with correct invariants */
    while i < v.Length
        invariant 0 <= i <= v.Length
        invariant sum == peekSum(v, i)
        invariant i > 0 ==> (forall k :: 0 <= k < i ==> v[k] <= maxSoFar)
        invariant i > 0 ==> maxSoFar in v[0..i]
        invariant i == 0 ==> maxSoFar == v[0]
    {
        /* code modified by LLM (iteration 1): Check if current element is a peak */
        if v[i] >= maxSoFar {
            /* code modified by LLM (iteration 1): Prove isPeek condition */
            assert forall k :: 0 <= k < i ==> v[i] >= v[k];
            assert isPeek(v, i);
            sum := sum + v[i];
            maxSoFar := v[i];
        } else {
            /* code modified by LLM (iteration 1): Prove not isPeek condition */
            assert exists k :: 0 <= k < i && v[i] < v[k];
            assert !isPeek(v, i);
        }
        
        i := i + 1;
    }
 }