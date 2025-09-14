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
lemma MinInArray(v: array<int>, i: int)
  requires 1 <= i <= v.Length
  ensures min(v, i) in v[0..i]
{
  if i == 1 {
    assert v[0] == min(v, i);
    assert v[0] in v[0..i];
  } else {
    MinInArray(v, i-1);
    if v[i-1] <= min(v, i-1) {
      assert min(v, i) == v[i-1];
      assert v[i-1] in v[0..i];
    } else {
      assert min(v, i) == min(v, i-1);
      assert min(v, i-1) in v[0..i-1];
      assert v[0..i-1] <= v[0..i];
    }
  }
}

lemma CountMinCorrect(v: array<int>, x: int, i: int, target: int)
  requires 0 <= i <= v.Length
  requires target in v[0..i]
  ensures countMin(v, target, i) > 0
{
  if i > 0 {
    if v[i-1] == target {
      assert countMin(v, target, i) == 1 + countMin(v, target, i-1);
    } else {
      assert target in v[0..i-1];
      CountMinCorrect(v, x, i-1, target);
    }
  }
}
// </vc-helpers>

// <vc-spec>
method mCountMin(v:array<int>) returns (c:int)
requires v.Length>0
ensures c==countMin(v,min(v,v.Length),v.Length)
//Implement and verify an O(v.Length) algorithm
// </vc-spec>
// <vc-code>
{
  var minVal := v[0];
  var i := 1;
  
  while i < v.Length
    invariant 1 <= i <= v.Length
    invariant minVal == min(v, i)
  {
    if v[i] < minVal {
      minVal := v[i];
    }
    i := i + 1;
  }
  
  c := 0;
  i := 0;
  
  while i < v.Length
    invariant 0 <= i <= v.Length
    invariant c == countMin(v, minVal, i)
  {
    if v[i] == minVal {
      c := c + 1;
    }
    i := i + 1;
  }
}
// </vc-code>

