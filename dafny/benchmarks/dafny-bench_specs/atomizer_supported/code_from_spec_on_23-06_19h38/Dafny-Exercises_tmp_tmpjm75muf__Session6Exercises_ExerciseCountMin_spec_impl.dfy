// ATOM 
function min(v:array<int>,i:int):int
 reads v
 requires 1<=i<=v.Length
 ensures forall k::0<=k<i==> v[k]>=min(v,i)
 {if (i==1) then v[0]
  else if (v[i-1]<=min(v,i-1)) then v[i-1]
  else min(v,i-1)
  }

// ATOM 
function countMin(v:array<int>,x:int, i:int):int
 reads v
  requires 0<=i<=v.Length
  ensures !(x in v[0..i]) ==> countMin(v,x,i)==0
  {
   if (i==0) then 0
   else if (v[i-1]==x) then 1+countMin(v,x,i-1)
   else countMin(v,x,i-1)
  
  }

//IMPL mCountMin
method mCountMin(v:array<int>) returns (c:int)
requires v.Length>0
ensures c==countMin(v,min(v,v.Length),v.Length)
{
    var minVal := v[0];
    c := 1;
    var i := 1;
    
    while i < v.Length
        invariant 1 <= i <= v.Length
        invariant minVal == min(v, i)
        invariant c == countMin(v, minVal, i)
    {
        if v[i] < minVal {
            minVal := v[i];
            c := 1;
        } else if v[i] == minVal {
            c := c + 1;
        }
        i := i + 1;
    }
}