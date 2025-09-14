predicate sorted(s : seq<int>) {
    forall u, w :: 0 <= u < w < |s| ==> s[u] <= s[w]
}

method binarySearch(v:array<int>, elem:int) returns (p:int)
 requires sorted(v[0..v.Length])
 ensures -1<=p<v.Length
 ensures (forall u::0<=u<=p ==> v[u]<=elem) && (forall w::p<w<v.Length ==> v[w]>elem)
{
  assume{:axiom} false;
}

// <vc-helpers>
function BinarySearchRec(s: seq<int>, elem: int, low: int, high: int): int
  requires sorted(s)
  requires 0 <= low <= high <= |s|
  decreases high - low
  ensures -1 <= BinarySearchRec(s, elem, low, high) <= high - 1
  ensures BinarySearchRec(s, elem, low, high) != -1 ==> s[BinarySearchRec(s, elem, low, high)] == elem && low <= BinarySearchRec(s, elem, low, high) < high
  ensures BinarySearchRec(s, elem, low, high) == -1 ==> !exists k :: low <= k < high && s[k] == elem
{
  if low >= high then -1
  else if s[low + (high - low) / 2] == elem then low + (high - low) / 2
  else if s[low + (high - low) / 2] < elem then BinarySearchRec(s, elem, low + (high - low) / 2 + 1, high)
  else BinarySearchRec(s, elem, low, low + (high - low) / 2)
}
// </vc-helpers>

// <vc-spec>
method search(v:array<int>,elem:int) returns (b:bool)
 requires sorted(v[0..v.Length])
ensures b==(elem in v[0..v.Length])
 //Implement by calling binary search function
// </vc-spec>
// <vc-code>
{
  b := BinarySearchRec(v[0..v.Length], elem, 0, v.Length) != -1;
}
// </vc-code>

//Recursive binary search