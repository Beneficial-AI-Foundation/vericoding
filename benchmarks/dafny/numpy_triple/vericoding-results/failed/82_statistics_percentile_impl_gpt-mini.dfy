// <vc-preamble>
// Helper function to count elements less than or equal to a value
ghost function CountLessOrEqual(arr: seq<real>, value: real): nat
{
  |set i | 0 <= i < |arr| && arr[i] <= value|
}

// Helper function to count elements greater than or equal to a value  
ghost function CountGreaterOrEqual(arr: seq<real>, value: real): nat
{
  |set i | 0 <= i < |arr| && arr[i] >= value|
}

// Helper function to get minimum value in array
ghost function MinValue(arr: seq<real>): real
  requires |arr| > 0
{
  if |arr| == 1 then arr[0]
  else if arr[0] <= MinValue(arr[1..]) then arr[0]
  else MinValue(arr[1..])
}

// Helper function to get maximum value in array
ghost function MaxValue(arr: seq<real>): real
  requires |arr| > 0
{
  if |arr| == 1 then arr[0]
  else if arr[0] >= MaxValue(arr[1..]) then arr[0]
  else MaxValue(arr[1..])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): concrete non-ghost MinOf that maintains prefix-min invariant */
method MinOf(arr: seq<real>) returns (m: real)
  requires |arr| > 0
  ensures exists i :: 0 <= i < |arr| && arr[i] == m
  ensures forall j :: 0 <= j < |arr| ==> m <= arr[j]
  ensures m == MinValue(arr)
{
  m := arr[0];
  var i := 1;
  while i < |arr|
    invariant 1 <= i <= |arr|
    invariant m == MinValue(arr[0..i])
    invariant exists t :: 0 <= t < i && arr[t] == m
    invariant forall j :: 0 <= j < i ==> m <= arr[j]
    decreases |arr| - i
  {
    if arr[i] < m {
      m := arr[i];
    }
    i := i + 1;
  }
}

/* helper modified by LLM (iteration 3): concrete non-ghost MaxOf that maintains prefix-max invariant */
method MaxOf(arr: seq<real>) returns (m: real)
  requires |arr| > 0
  ensures exists i :: 0 <= i < |arr| && arr[i] == m
  ensures forall j :: 0 <= j < |arr| ==> m >= arr[j]
  ensures m == MaxValue(arr)
{
  m := arr[0];
  var i := 1;
  while i < |arr|
    invariant 1 <= i <= |arr|
    invariant m == MaxValue(arr[0..i])
    invariant exists t :: 0 <= t < i && arr[t] == m
    invariant forall j :: 0 <= j < i ==> m >= arr[j]
    decreases |arr| - i
  {
    if arr[i] > m {
      m := arr[i];
    }
    i := i + 1;
  }
}

/* helper modified by LLM (iteration 3): concrete count of <= to relate runtime count to ghost CountLessOrEqual */
method CountLE(arr: seq<real>, value: real) returns (cnt: nat)
  ensures cnt == CountLessOrEqual(arr, value)
{
  cnt := 0;
  var j := 0;
  while j < |arr|
    invariant 0 <= j <= |arr|
    invariant cnt == |set t | 0 <= t < j && arr[t] <= value|
    decreases |arr| - j
  {
    if arr[j] <= value {
      cnt := cnt + 1;
    }
    j := j + 1;
  }
}

/* helper modified by LLM (iteration 3): concrete count of >= to relate runtime count to ghost CountGreaterOrEqual */
method CountGE(arr: seq<real>, value: real) returns (cnt: nat)
  ensures cnt == CountGreaterOrEqual(arr, value)
{
  cnt := 0;
  var j := 0;
  while j < |arr|
    invariant 0 <= j <= |arr|
    invariant cnt == |set t | 0 <= t < j && arr[t] >= value|
    decreases |arr| - j
  {
    if arr[j] >= value {
      cnt := cnt + 1;
    }
    j := j + 1;
  }
}

// </vc-helpers>

// <vc-spec>
method Percentile(arr: seq<real>, q: real) returns (result: real)
  // Input validation: array must be non-empty and q must be valid percentile
  requires |arr| > 0
  requires 0.0 <= q <= 100.0
  
  // The result must be bounded by the array's min and max values
  ensures MinValue(arr) <= result <= MaxValue(arr)
  
  // Percentile property: at least q% of values are <= result
  ensures CountLessOrEqual(arr, result) as real >= (q / 100.0) * |arr| as real
  
  // Percentile property: at least (100-q)% of values are >= result  
  ensures CountGreaterOrEqual(arr, result) as real >= ((100.0 - q) / 100.0) * |arr| as real
  
  // Special case: 0th percentile is the minimum
  ensures q == 0.0 ==> result == MinValue(arr)
  
  // Special case: 100th percentile is the maximum
  ensures q == 100.0 ==> result == MaxValue(arr)
  
  // For any percentile, there exists at least one element <= result and >= result
  ensures exists i :: 0 <= i < |arr| && arr[i] <= result
  ensures exists i :: 0 <= i < |arr| && arr[i] >= result
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): select k-th order statistic by concrete counts and helper methods */
{
  if q == 0.0 {
    result := MinOf(arr);
    return;
  }
  if q == 100.0 {
    result := MaxOf(arr);
    return;
  }

  var n := |arr|;
  var mn := MinOf(arr);
  var mx := MaxOf(arr);

  // compute k = ceil((q/100) * n)
  var k := 0;
  while (k as real) < (q / 100.0) * (n as real)
    invariant 0 <= k <= n
    decreases n - k
  {
    k := k + 1;
  }

  var i := 0;
  while i < n
    invariant 0 <= i <= n
    decreases n - i
  {
    var cntLE := CountLE(arr, arr[i]);
    if cntLE >= k {
      var cntGE := CountGE(arr, arr[i]);
      if cntGE >= n - k + 1 {
        // arr[i] is a valid percentile value
        result := arr[i];
        return;
      }
    }
    i := i + 1;
  }

  // Fallback (the loop is expected to find a value); return max to satisfy bounds
  result := mx;
}

// </vc-code>
