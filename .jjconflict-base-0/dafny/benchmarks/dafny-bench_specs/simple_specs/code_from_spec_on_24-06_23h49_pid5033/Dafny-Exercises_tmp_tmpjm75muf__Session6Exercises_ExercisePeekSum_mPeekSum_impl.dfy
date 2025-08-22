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


//IMPL mPeekSum

/* code modified by LLM (iteration 4): Added helper function to compute maximum up to index */
function maxUpTo(v: array<int>, i: int): int
  reads v
  requires 0 <= i < v.Length
{
  if i == 0 then v[0]
  else if v[i] >= maxUpTo(v, i-1) then v[i]
  else maxUpTo(v, i-1)
}

/* code modified by LLM (iteration 4): Added lemma to establish maxUpTo properties */
lemma maxUpToProperties(v: array<int>, i: int)
  requires 0 <= i < v.Length
  ensures maxUpTo(v, i) >= v[i]
  ensures forall k :: 0 <= k <= i ==> maxUpTo(v, i) >= v[k]
{
  if i == 0 {
    // Base case
  } else {
    maxUpToProperties(v, i-1);
  }
}

/* code modified by LLM (iteration 4): Added lemma to connect isPeek with maxUpTo */
lemma isPeekEquivalence(v: array<int>, i: int)
  requires 0 <= i < v.Length
  ensures isPeek(v, i) <==> (v[i] == maxUpTo(v, i))
{
  maxUpToProperties(v, i);
  
  if isPeek(v, i) {
    // If isPeek(v, i), then v[i] >= v[k] for all k in [0, i]
    assert forall k :: 0 <= k < i ==> v[i] >= v[k];
    assert v[i] >= v[i];
    if i > 0 {
      assert v[i] >= maxUpTo(v, i-1);
      assert maxUpTo(v, i) == v[i];
    }
  }
  
  if v[i] == maxUpTo(v, i) {
    // If v[i] == maxUpTo(v, i), then isPeek(v, i)
    assert forall k :: 0 <= k <= i ==> maxUpTo(v, i) >= v[k];
    assert forall k :: 0 <= k < i ==> v[i] >= v[k];
  }
}

method mPeekSum(v:array<int>) returns (sum:int)
 requires v.Length>0
 ensures sum==peekSum(v,v.Length)
 //Implement and verify an O(v.Length) algorithm to solve this problem
 {
   /* code modified by LLM (iteration 4): Corrected initialization and algorithm */
   sum := 0;
   var maxSoFar := v[0];
   var i := 1;
   
   // Handle first element (always a peek)
   isPeekEquivalence(v, 0);
   assert isPeek(v, 0);
   sum := v[0];
   
   while i < v.Length
     /* code modified by LLM (iteration 4): Fixed loop invariants */
     invariant 1 <= i <= v.Length
     invariant maxSoFar == maxUpTo(v, i-1)
     invariant sum == peekSum(v, i)
   {
     /* code modified by LLM (iteration 4): Fixed peek detection logic */
     isPeekEquivalence(v, i);
     maxUpToProperties(v, i);
     
     if v[i] >= maxSoFar {
       // v[i] is a peak
       assert maxSoFar == maxUpTo(v, i-1);
       assert v[i] >= maxUpTo(v, i-1);
       assert maxUpTo(v, i) == v[i];
       assert isPeek(v, i);
       sum := sum + v[i];
       maxSoFar := v[i];
     } else {
       // v[i] is not a peak
       assert v[i] < maxSoFar;
       assert maxSoFar == maxUpTo(v, i-1);
       assert maxUpTo(v, i) == maxUpTo(v, i-1);
       assert v[i] != maxUpTo(v, i);
       assert !isPeek(v, i);
       // sum remains the same
     }
     
     i := i + 1;
   }
 }