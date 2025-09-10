function count_negative_temp_days(temps: seq<int>): int
{
    if |temps| == 0 then 0
    else (if temps[0] < 0 then 1 else 0) + count_negative_temp_days(temps[1..])
}

// <vc-helpers>
lemma NegativeDaysLemma(temps: seq<int>, start: int, end: int) 
  requires 0 <= start <= end <= |temps|
  ensures count_negative_temp_days(temps[start..end]) >= 0
  decreases end - start
{
  if start < end {
    NegativeDaysLemma(temps, start + 1, end);
  }
}

lemma SlicePreservesCount(temps: seq<int>, start: int, mid: int, end: int)
  requires 0 <= start <= mid <= end <= |temps|
  ensures count_negative_temp_days(temps[start..end]) == 
          count_negative_temp_days(temps[start..mid]) + count_negative_temp_days(temps[mid..end])
  decreases end - start
{
  if start < mid {
    SlicePreservesCount(temps, start + 1, mid, end);
  }
}

lemma CountNegativeTempDaysNonNegative(temps: seq<int>)
  ensures count_negative_temp_days(temps) >= 0
{
  // This is trivially true by the structure of count_negative_temp_days
}

lemma CountUpdateLemma(temps: seq<int>, i: int)
  requires 0 <= i <= |temps|
  ensures count_negative_temp_days(temps[0..i+1]) == 
          count_negative_temp_days(temps[0..i]) + (if i < |temps| && temps[i] < 0 then 1 else 0)
  decreases |temps| - i
{
  if i < |temps| {
    SlicePreservesCount(temps, 0, i, i+1);
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, temps: seq<int>) returns (result: int)
  requires n >= 1
  requires k >= 0 && k <= n
  requires |temps| == n
  requires forall i :: 0 <= i < n ==> -20 <= temps[i] <= 20
  ensures result == -1 <==> count_negative_temp_days(temps) > k
  ensures result != -1 ==> result >= 0
  ensures result == 0 ==> forall i :: 0 <= i < n ==> temps[i] >= 0
  ensures result > 0 ==> exists i :: 0 <= i < n && temps[i] < 0
// </vc-spec>
// <vc-code>
{
  var count := 0;
  var i := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant count == count_negative_temp_days(temps[0..i])
  {
    CountUpdateLemma(temps, i);
    if temps[i] < 0 {
      count := count + 1;
    }
    i := i + 1;
  }
  
  CountNegativeTempDaysNonNegative(temps);
  
  if count > k {
    result := -1;
  } else {
    result := 0;
    i := 0;
    var found := false;
    
    while i < n
      invariant 0 <= i <= n
      invariant forall j :: 0 <= j < i ==> !found || j != result ==> temps[j] >= 0
      invariant !found ==> result == 0
      invariant found ==> 0 <= result < i && temps[result] < 0
      invariant !found ==> count_negative_temp_days(temps[0..i]) == 0
      invariant found ==> count_negative_temp_days(temps[0..i]) == 1
    {
      if temps[i] < 0 && !found {
        result := i;
        found := true;
      }
      i := i + 1;
    }
    
    if !found {
      result := 0;
    }
  }
}
// </vc-code>

