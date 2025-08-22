//ATOM
// Ex1
method copyArr(a : array<int>, l : int, r : int) returns (ret : array<int>)
 requires 0 <= l < r <= a.Length 
 ensures ret[..] == a[l..r]
{
  /* code modified by LLM (iteration 1): Fixed syntax error and implemented proper array copying */
  ret := new int[r - l];
  var i := 0;
  while i < r - l
    invariant 0 <= i <= r - l
    invariant ret[..i] == a[l..l+i]
  {
    ret[i] := a[l + i];
    i := i + 1;
  }
}

//ATOM
function sorted(s : seq<int>) : bool {
 forall k1, k2 :: 0 <= k1 <= k2 < |s| ==> s[k1] <= s[k2]
}

/* code modified by LLM (iteration 4): Added helper lemma to establish multiset properties */
lemma MergePreservesElements(a: array<int>, l: int, m: int, r: int, left: array<int>, right: array<int>)
  requires 0 <= l < m < r <= a.Length
  requires left[..] == a[l..m]
  requires right[..] == a[m..r]
  ensures multiset(left[..]) + multiset(right[..]) == multiset(a[l..r])
{
  assert a[l..r] == a[l..m] + a[m..r];
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
    var left := copyArr(a, l, m);
    var right := copyArr(a, m, r);
    
    /* code modified by LLM (iteration 4): Added lemma call to establish multiset property */
    MergePreservesElements(a, l, m, r, left, right);
    
    var i := 0;
    var j := 0;
    var k := l;
    
    /* code modified by LLM (iteration 4): Enhanced invariants with multiset properties and stronger sorting conditions */
    while i < left.Length && j < right.Length
        invariant 0 <= i <= left.Length
        invariant 0 <= j <= right.Length
        invariant k == l + i + j
        invariant l <= k <= r
        invariant a[..l] == old(a[..l])
        invariant a[r..] == old(a[r..])
        invariant left[..] == old(a[l..m])
        invariant right[..] == old(a[m..r])
        invariant sorted(left[..])
        invariant sorted(right[..])
        invariant sorted(a[l..k])
        invariant multiset(a[l..k]) == multiset(left[..i]) + multiset(right[..j])
        invariant i < left.Length && j < right.Length && k > l ==> a[k-1] <= left[i] && a[k-1] <= right[j]
    {
        if left[i] <= right[j] {
            a[k] := left[i];
            i := i + 1;
        } else {
            a[k] := right[j];
            j := j + 1;
        }
        k := k + 1;
    }
    
    /* code modified by LLM (iteration 4): Enhanced invariants for remaining left elements */
    while i < left.Length
        invariant 0 <= i <= left.Length
        invariant j == right.Length
        invariant k == l + i + j
        invariant l <= k <= r
        invariant a[..l] == old(a[..l])
        invariant a[r..] == old(a[r..])
        invariant left[..] == old(a[l..m])
        invariant right[..] == old(a[m..r])
        invariant sorted(left[..])
        invariant sorted(a[l..k])
        invariant multiset(a[l..k]) == multiset(left[..i]) + multiset(right[..])
        invariant i < left.Length && k > l ==> a[k-1] <= left[i]
    {
        a[k] := left[i];
        i := i + 1;
        k := k + 1;
    }
    
    /* code modified by LLM (iteration 4): Enhanced invariants for remaining right elements */
    while j < right.Length
        invariant i == left.Length
        invariant 0 <= j <= right.Length
        invariant k == l + i + j
        invariant l <= k <= r
        invariant a[..l] == old(a[..l])
        invariant a[r..] == old(a[r..])
        invariant left[..] == old(a[l..m])
        invariant right[..] == old(a[m..r])
        invariant sorted(right[..])
        invariant sorted(a[l..k])
        invariant multiset(a[l..k]) == multiset(left[..]) + multiset(right[..j])
        invariant j < right.Length && k > l ==> a[k-1] <= right[j]
    {
        a[k] := right[j];
        j := j + 1;
        k := k + 1;
    }
    
    /* code modified by LLM (iteration 4): Added assertion to help prove final postcondition */
    assert k == r;
    assert multiset(a[l..r]) == multiset(left[..]) + multiset(right[..]);
    assert multiset(left[..]) + multiset(right[..]) == multiset(old(a[l..r]));
}