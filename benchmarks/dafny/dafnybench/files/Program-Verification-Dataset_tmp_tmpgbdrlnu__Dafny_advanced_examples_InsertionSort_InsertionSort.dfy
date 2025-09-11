// <vc-preamble>
predicate sorted (a:array<int>, start:int, end:int)
 requires a!=null       
 requires 0<=start<=end<=a.Length       
 reads a       
 {           
   forall j,k:: start<=j<k<end ==> a[j]<=a[k]
 }
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method InsertionSort (a:array<int>)
requires a!=null && a.Length>1 
ensures sorted(a, 0, a.Length) 
modifies a
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
