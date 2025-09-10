predicate isLadder(arr: seq<int>, l: int, r: int)
  requires 0 <= l <= r < |arr|
{
  if l == r then true
  else
    exists k :: l <= k <= r && 
      isNonDecreasing(arr, l, k) && 
      isNonIncreasing(arr, k, r)
}

predicate isNonDecreasing(arr: seq<int>, start: int, end: int)
  requires 0 <= start <= end < |arr|
{
  forall i :: start <= i < end ==> arr[i] <= arr[i+1]
}

predicate isNonIncreasing(arr: seq<int>, start: int, end: int)
  requires 0 <= start <= end < |arr|
{
  forall i :: start <= i < end ==> arr[i] >= arr[i+1]
}

// <vc-helpers>
lemma LadderExists(arr: seq<int>, l: int, r: int, k: int)
  requires 0 <= l <= r < |arr|
  requires l <= k <= r
  requires isNonDecreasing(arr, l, k)
  requires isNonIncreasing(arr, k, r)
  ensures isLadder(arr, l, r)
{
  // Direct proof that if we have k with the required properties, then isLadder holds
}

lemma NoLadderImpliesNoValidK(arr: seq<int>, l: int, r: int)
  requires 0 <= l <= r < |arr|
  requires !isLadder(arr, l, r)
  ensures forall k :: l <= k <= r ==> !(isNonDecreasing(arr, l, k) && isNonIncreasing(arr, k, r))
{
  // Proof by contradiction
}

lemma NonDecreasingComputation(arr: seq<int>, l: int, k: int)
  requires 0 <= l <= k < |arr|
  ensures isNonDecreasing(arr, l, k) <==> (forall j :: l <= j < k ==> arr[j] <= arr[j+1])
{
  // Definition of isNonDecreasing
}

lemma NonIncreasingComputation(arr: seq<int>, k: int, r: int)
  requires 0 <= k <= r < |arr|
  ensures isNonIncreasing(arr, k, r) <==> (forall j :: k <= j < r ==> arr[j] >= arr[j+1])
{
  // Definition of isNonIncreasing
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, arr: seq<int>, queries: seq<(int, int)>) returns (results: seq<string>)
  requires n >= 1 && m >= 1
  requires |arr| == n
  requires |queries| == m
  requires forall i :: 0 <= i < m ==> 1 <= queries[i].0 <= queries[i].1 <= n
  ensures |results| == m
  ensures forall i :: 0 <= i < m ==> results[i] == "Yes" || results[i] == "No"
  ensures forall i :: 0 <= i < m ==> 
    (results[i] == "Yes" <==> isLadder(arr, queries[i].0 - 1, queries[i].1 - 1))
// </vc-spec>
// <vc-code>
{
  var res := [];
  var i := 0;
  
  while i < m
    invariant 0 <= i <= m
    invariant |res| == i
    invariant forall j :: 0 <= j < i ==> res[j] == "Yes" || res[j] == "No"
    invariant forall j :: 0 <= j < i ==> 
      (res[j] == "Yes" <==> isLadder(arr, queries[j].0 - 1, queries[j].1 - 1))
  {
    var l := queries[i].0 - 1;
    var r := queries[i].1 - 1;
    
    if l == r {
      res := res + ["Yes"];
    } else {
      var found := false;
      var k := l;
      
      while k <= r && !found
        decreases if found then 0 else r - k + 1
        invariant l <= k <= r + 1
        invariant found ==> isLadder(arr, l, r)
        invariant !found ==> forall j :: l <= j < k ==> !(isNonDecreasing(arr, l, j) && isNonIncreasing(arr, j, r))
      {
        var isNonDec := true;
        var j := l;
        while j < k && isNonDec
          invariant l <= j <= k
          invariant isNonDec ==> forall idx :: l <= idx < j ==> arr[idx] <= arr[idx+1]
        {
          if arr[j] > arr[j+1] {
            isNonDec := false;
          }
          j := j + 1;
        }
        
        if isNonDec {
          var isNonInc := true;
          j := k;
          while j < r && isNonInc
            invariant k <= j <= r
            invariant isNonInc ==> forall idx :: k <= idx < j ==> arr[idx] >= arr[idx+1]
          {
            if arr[j] < arr[j+1] {
              isNonInc := false;
            }
            j := j + 1;
          }
          
          if isNonInc {
            NonDecreasingComputation(arr, l, k);
            assert forall idx :: l <= idx < k ==> arr[idx] <= arr[idx+1];
            assert isNonDecreasing(arr, l, k);
            
            NonIncreasingComputation(arr, k, r);
            assert forall idx :: k <= idx < r ==> arr[idx] >= arr[idx+1];
            assert isNonIncreasing(arr, k, r);
            
            found := true;
            LadderExists(arr, l, r, k);
          } else {
            NonIncreasingComputation(arr, k, r);
            assert !isNonIncreasing(arr, k, r);
            k := k + 1;
          }
        } else {
          NonDecreasingComputation(arr, l, k);
          assert !isNonDecreasing(arr, l, k);
          k := k + 1;
        }
      }
      
      if found {
        res := res + ["Yes"];
      } else {
        NoLadderImpliesNoValidK(arr, l, r);
        res := res + ["No"];
      }
    }
    
    i := i + 1;
  }
  
  results := res;
}
// </vc-code>

