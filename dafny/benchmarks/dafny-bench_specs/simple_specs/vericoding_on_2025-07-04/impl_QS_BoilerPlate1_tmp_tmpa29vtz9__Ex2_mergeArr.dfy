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
function sorted(s : seq<int>) : bool {
 forall k1, k2 :: 0 <= k1 <= k2 < |s| ==> s[k1] <= s[k2]
}


//IMPL Ex2

method mergeArr(a : array<int>, l : int, m : int, r : int)
 requires 0 <= l < m < r <= a.Length 
 requires sorted(a[l..m]) && sorted(a[m..r])
 ensures sorted(a[l..r]) 
 ensures a[..l] == old(a[..l])
 ensures a[r..] == old(a[r..])
 modifies a 
{
  var temp := copyArr(a, l, r);
  var i := 0;
  var j := m - l;
  var k := l;
  
  /* code modified by LLM (iteration 1): Simplified and corrected loop invariants for proper verification */
  while k < r
    invariant l <= k <= r
    invariant 0 <= i <= m - l
    invariant m - l <= j <= r - l
    invariant i + j == k - l + (m - l)
    invariant a[..l] == old(a[..l])
    invariant a[r..] == old(a[r..])
    invariant temp[..] == old(a[l..r])
    invariant sorted(a[l..k])
    invariant forall x :: l <= x < k ==> (i < m - l ==> a[x] <= temp[i])
    invariant forall x :: l <= x < k ==> (j < r - l ==> a[x] <= temp[j])
    decreases r - k
  {
    /* code modified by LLM (iteration 1): Added assertions to help verification and fixed merge logic */
    if i >= m - l {
      assert j < r - l;
      a[k] := temp[j];
      j := j + 1;
    } else if j >= r - l {
      assert i < m - l;
      a[k] := temp[i];
      i := i + 1;
    } else if temp[i] <= temp[j] {
      a[k] := temp[i];
      i := i + 1;
    } else {
      a[k] := temp[j];
      j := j + 1;
    }
    
    /* code modified by LLM (iteration 1): Added assertion to maintain sortedness invariant */
    if k > l {
      assert a[k-1] <= a[k];
    }
    
    k := k + 1;
  }
}