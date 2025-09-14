//Algorithm 1: From left to right return the first

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method mmaximum1(v:array<int>) returns (i:int) 
requires v.Length>0
ensures 0<=i<v.Length 
ensures forall k:: 0<=k<v.Length ==> v[i]>=v[k]
// </vc-spec>
// <vc-code>
{
   i := 0;
   var k := 1;
   while k < v.Length
     invariant 0 <= i < k <= v.Length
     invariant forall l :: 0 <= l < k ==> v[i] >= v[l]
   {
     if v[k] > v[i]
     {
       i := k;
     }
     k := k + 1;
   }
   return i;
}
// </vc-code>

//Algorithm 2: From right to left return the last




//Algorithm : from left to right
//Algorithm : from right to left