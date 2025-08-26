predicate sorted(s : seq<int>) {
    forall u, w :: 0 <= u < w < |s| ==> s[u] <= s[w]
}

// <vc-spec>
method binarySearch(v:array<int>, elem:int) returns (p:int)
 requires sorted(v[0..v.Length])
 ensures -1<=p<v.Length
 ensures (forall u::0<=u<=p ==> v[u]<=elem) && (forall w::p<w<v.Length ==> v[w]>elem)
 {
  var c,f:=0,v.Length-1;
  while (c<=f)
     decreases f-c
     invariant 0<=c<=v.Length && -1<=f<=v.Length-1 && c<=f+1
     invariant (forall u::0<=u<c ==> v[u]<=elem) && 
               (forall w::f<w<v.Length ==> v[w]>elem)
  {
   var m:=(c+f)/2;
   if (v[m]<=elem) 
        {c:=m+1;}
   else {f:=m-1;}
   }
   p:=c-1;


 }






//Recursive binary search

// <vc-helpers>
method recursiveBinarySearch(v:array<int>, elem:int, left:int, right:int) returns (b:bool, p:int)
  requires sorted(v[0..v.Length])
  requires 0 <= left <= right + 1 <= v.Length
  requires forall u :: 0 <= u < left ==> v[u] < elem
  requires forall w :: right < w < v.Length ==> v[w] > elem
  ensures 0 <= p <= v.Length
  ensures b == (elem in v[left..right+1])
  ensures b ==> left <= p <= right && v[p] == elem
  ensures !b ==> (forall u :: 0 <= u < p ==> v[u] < elem) && 
                 (forall w :: p <= w < v.Length ==> v[w] > elem)
  decreases right - left + 1
{
  if left > right {
    b := false;
    p := left;
    return;
  }
  
  var mid := left + (right - left) / 2;
  
  if v[mid] == elem {
    b := true;
    p := mid;
  } else if v[mid] < elem {
    b, p := recursiveBinarySearch(v, elem, mid + 1, right);
  } else {
    b, p := recursiveBinarySearch(v, elem, left, mid - 1);
  }
}
// </vc-helpers>

method otherbSearch(v:array<int>, elem:int) returns (b:bool,p:int)
 requires sorted(v[0..v.Length])
 ensures 0<=p<=v.Length
 ensures b == (elem in v[0..v.Length])
 ensures b ==> p<v.Length && v[p]==elem
 ensures !b ==> (forall u::0<=u<p ==> v[u]<elem) && 
               (forall w::p<=w<v.Length ==> v[w]>elem)
 //Implement and verify
// </vc-spec>
// <vc-code>
{
  if v.Length == 0 {
    b := false;
    p := 0;
    return;
  }
  
  b, p := recursiveBinarySearch(v, elem, 0, v.Length - 1);
}
// </vc-code>