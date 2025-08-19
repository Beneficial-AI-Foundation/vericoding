//ATOM

// Ex1

method copyArr(a : array<int>, l : int, r : int) returns (ret : array<int>)
 requires 0 <= l < r <= a.Length 
 ensures ret[..] == a[l..r]
{
  ret := [];
  assume ret[..] == a[l..r];
  return ret;
}

//ATOM

method sortAux(a : array<int>, l : int, r : int)
 ensures sorted(a[l..r])
 ensures a[..l] == old(a[..l])
 ensures a[r..] == old(a[r..])
 requires 0 <= l < r <= a.Length
 modifies a
{
  assume sorted(a[l..r]);
  assume a[..l] == old(a[..l]);
  assume a[r..] == old(a[r..]);
}

//ATOM
function sorted(s : seq<int>) : bool {
 forall k1, k2 :: 0 <= k1 <= k2 < |s| ==> s[k1] <= s[k2]
}

//ATOM

// Ex2

method mergeArr(a : array<int>, l : int, m : int, r : int)
 requires 0 <= l < m < r <= a.Length 
 requires sorted(a[l..m]) && sorted(a[m..r])
 ensures sorted(a[l..r]) 
 ensures a[..l] == old(a[..l])
 ensures a[r..] == old(a[r..])
 modifies a 
{
  assume sorted(a[l..r]);
  assume a[..l] == old(a[..l]);
  assume a[r..] == old(a[r..]);
}

/* code modified by LLM (iteration 1): Added helper lemma before the method to fix compilation order */
lemma lemmaSmallArraysSorted(s: seq<int>)
  requires |s| <= 1
  ensures sorted(s)
{
  /* code modified by LLM (iteration 1): Proof that sequences of length <= 1 are sorted */
  if |s| == 0 {
    // Empty sequence: no pairs (k1, k2) exist, so the forall condition is vacuously true
  } else {
    // |s| == 1: only pair is (0, 0), and s[0] <= s[0] is trivially true
    assert |s| == 1;
    assert forall k1, k2 :: 0 <= k1 <= k2 < |s| ==> k1 == 0 && k2 == 0;
    assert s[0] <= s[0];
  }
}

//IMPL 

// Ex3

method sort(a : array<int>) 
 ensures sorted(a[..])
 modifies a
{
  if a.Length > 1 {
    sortAux(a, 0, a.Length);
  }
  else {
    /* code modified by LLM (iteration 1): Fixed lemma call with proper sequence conversion */
    lemmaSmallArraysSorted(a[..]);
  }
}