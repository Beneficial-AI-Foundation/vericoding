// <vc-preamble>
function Sum(a: seq<int>, s: int, t: int): int
  requires 0 <= s <= t <= |a|
{
  if s == t then 0 else Sum(a, s, t-1) + a[t-1]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added lemmas for minimum subarray tracking */
lemma SumExtension(a: seq<int>, s: int, t: int)
  requires 0 <= s <= t < |a|
  ensures Sum(a, s, t+1) == Sum(a, s, t) + a[t]
{
}

lemma EmptySum(a: seq<int>, i: int)
  requires 0 <= i <= |a|
  ensures Sum(a, i, i) == 0
{
}

lemma SingleSum(a: seq<int>, i: int)
  requires 0 <= i < |a|
  ensures Sum(a, i, i+1) == a[i]
{
}

lemma MinExistsInPrefix(a: seq<int>, i: int, minVal: int, minStart: int, minEnd: int)
  requires 0 <= i <= |a|
  requires 0 <= minStart <= minEnd <= |a|
  requires Sum(a, minStart, minEnd) == minVal
  requires forall p, q :: 0 <= p <= q <= i ==> Sum(a, p, q) >= minVal
  ensures forall p, q :: 0 <= p <= q <= |a| ==> Sum(a, p, q) >= minVal ==> forall r, s :: 0 <= r <= s <= |a| ==> Sum(a, r, s) >= minVal
{
}
// </vc-helpers>

// <vc-spec>
method minSubArraySum(a: seq<int>) returns (s: int)

  ensures forall p,q :: 0 <= p <= q <= |a| ==> Sum(a, p, q) >= s
  ensures exists k, m :: 0 <= k <= m <= |a| && s == Sum(a, k, m)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Brute force approach with explicit tracking */
  if |a| == 0 {
    s := 0;
    return;
  }
  
  s := Sum(a, 0, 0);
  
  var i := 0;
  while i <= |a|
    invariant 0 <= i <= |a| + 1
    invariant exists k, m :: 0 <= k <= m <= |a| && s == Sum(a, k, m)
    invariant forall p, q :: 0 <= p <= q <= i ==> Sum(a, p, q) >= s
  {
    if i == |a| {
      break;
    }
    
    var j := i;
    while j <= |a|
      invariant i <= j <= |a| + 1
      invariant exists k, m :: 0 <= k <= m <= |a| && s == Sum(a, k, m)
      invariant forall p, q :: 0 <= p <= q <= i ==> Sum(a, p, q) >= s
      invariant forall q :: i <= q < j ==> Sum(a, i, q) >= s
    {
      if j == |a| + 1 {
        break;
      }
      
      var currentSum := Sum(a, i, j);
      if currentSum < s {
        s := currentSum;
      }
      
      j := j + 1;
    }
    
    i := i + 1;
  }
}
// </vc-code>
