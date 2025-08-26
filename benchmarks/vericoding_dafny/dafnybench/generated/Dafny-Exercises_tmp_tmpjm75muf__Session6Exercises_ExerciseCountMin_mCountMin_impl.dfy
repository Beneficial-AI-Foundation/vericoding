// <vc-spec>
function min(v:array<int>,i:int):int
decreases i
 reads v
 requires 1<=i<=v.Length
 ensures forall k::0<=k<i==> v[k]>=min(v,i)
 {if (i==1) then v[0]
  else if (v[i-1]<=min(v,i-1)) then v[i-1]
  else min(v,i-1)
  }


function countMin(v:array<int>,x:int, i:int):int
decreases i
 reads v
  requires 0<=i<=v.Length
  ensures !(x in v[0..i]) ==> countMin(v,x,i)==0
  {
   if (i==0) then 0
   else if (v[i-1]==x) then 1+countMin(v,x,i-1)
   else countMin(v,x,i-1)

  }

// <vc-helpers>
lemma countMinLemma(v: array<int>, x: int, i: int, j: int)
  requires 0 <= i <= j <= v.Length
  requires forall k :: i <= k < j ==> v[k] != x
  ensures countMin(v, x, j) == countMin(v, x, i)
  decreases j - i
{
  if i == j {
    // Base case: ranges are equal
  } else {
    // Inductive case
    countMinLemma(v, x, i, j-1);
  }
}

lemma countMinExtend(v: array<int>, x: int, i: int)
  requires 0 <= i < v.Length
  ensures countMin(v, x, i+1) == countMin(v, x, i) + (if v[i] == x then 1 else 0)
{
  // Follows directly from definition
}

lemma minExtend(v: array<int>, i: int)
  requires 1 <= i < v.Length
  ensures min(v, i+1) == if v[i] <= min(v, i) then v[i] else min(v, i)
{
  // Follows directly from definition
}
// </vc-helpers>

method mCountMin(v:array<int>) returns (c:int)
requires v.Length>0
ensures c==countMin(v,min(v,v.Length),v.Length)
//Implement and verify an O(v.Length) algorithm
// </vc-spec>
// <vc-code>
{
  var minVal := v[0];
  var count := 1;
  var i := 1;
  
  // Find minimum and count in single pass
  while i < v.Length
    invariant 1 <= i <= v.Length
    invariant minVal == min(v, i)
    invariant count == countMin(v, minVal, i)
  {
    minExtend(v, i);
    if v[i] < minVal {
      countMinLemma(v, v[i], 0, i);
      minVal := v[i];
      count := 1;
    } else if v[i] == minVal {
      countMinExtend(v, minVal, i);
      count := count + 1;
    } else {
      countMinExtend(v, minVal, i);
    }
    i := i + 1;
  }
  
  c := count;
}
// </vc-code>