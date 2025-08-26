function sorted(s : seq<int>) : bool {
  forall k1, k2 :: 0 <= k1 <= k2 < |s| ==> s[k1] <= s[k2]
}


// Ex1

method copyArr(a : array<int>, l : int, r : int) returns (ret : array<int>)
  requires 0 <= l < r <= a.Length 
  ensures ret[..] == old(a[..])
{
  var size := r - l;
  ret := new int[size];
  var i := 0;

  while(i < size)
    invariant a[..] == old(a[..])
    invariant 0 <= i <= size
    invariant ret[..i] == a[l..(l + i)]
    decreases size - i
  {
    ret[i] := a[i + l];
    i := i + 1;
  }
  return;
}


// Ex2

// <vc-helpers>
lemma sortedExtend(s: seq<int>, x: int)
  requires sorted(s)
  requires |s| == 0 || s[|s|-1] <= x
  ensures sorted(s + [x])
{
}

lemma sortedImpliesOrdered(s: seq<int>, i: int, j: int)
  requires sorted(s)
  requires 0 <= i <= j < |s|
  ensures s[i] <= s[j]
{
}
// </vc-helpers>

method mergeArr(a : array<int>, l : int, m : int, r : int)
  requires 0 <= l < m < r <= a.Length  
  requires sorted(a[l..m]) && sorted(a[m..r])
  ensures sorted(a[l..r]) 
  ensures a[..l] == old(a[..l])
  ensures a[r..] == old(a[r..])
  modifies a
// </vc-spec>
// <vc-code>
{
  var leftArr := copyArr(a, l, m);
  var rightArr := copyArr(a, m, r);
  
  var i := 0; // index for leftArr;
  var j := 0; // index for rightArr;
  var k := l; // index for merged array;
  
  while i < leftArr.Length && j < rightArr.Length
    invariant 0 <= i <= leftArr.Length
    invariant 0 <= j <= rightArr.Length
    invariant l <= k <= r
    invariant k == l + i + j
    invariant leftArr[..] == old(a[l..m])
    invariant rightArr[..] == old(a[m..r])
    invariant a[..l] == old(a[..l])
    invariant a[r..] == old(a[r..])
    invariant sorted(a[l..k])
    invariant i < leftArr.Length ==> (forall idx :: l <= idx < k ==> a[idx] <= leftArr[i])
    invariant j < rightArr.Length ==> (forall idx :: l <= idx < k ==> a[idx] <= rightArr[j])
    invariant sorted(leftArr[..])
    invariant sorted(rightArr[..])
    decreases leftArr.Length + rightArr.Length - i - j
  {
    if leftArr[i] <= rightArr[j] {
      a[k] := leftArr[i];
      assert k == l ==> |a[l..k]| == 0;
      assert k > l ==> a[l..k][|a[l..k]|-1] == a[k-1];
      if k > l {
        assert j < rightArr.Length ==> a[k-1] <= rightArr[j];
        assert a[k-1] <= leftArr[i];
      }
      sortedExtend(a[l..k], leftArr[i]);
      i := i + 1;
    } else {
      a[k] := rightArr[j];
      assert k == l ==> |a[l..k]| == 0;
      assert k > l ==> a[l..k][|a[l..k]|-1] == a[k-1];
      if k > l {
        assert i < leftArr.Length ==> a[k-1] <= leftArr[i];
        assert a[k-1] <= rightArr[j];
      }
      sortedExtend(a[l..k], rightArr[j]);
      j := j + 1;
    }
    k := k + 1;
  }
  
  while i < leftArr.Length
    invariant 0 <= i <= leftArr.Length
    invariant 0 <= j <= rightArr.Length
    invariant l <= k <= r
    invariant k == l + i + j
    invariant leftArr[..] == old(a[l..m])
    invariant rightArr[..] == old(a[m..r])
    invariant a[..l] == old(a[..l])
    invariant a[r..] == old(a[r..])
    invariant sorted(a[l..k])
    invariant j < rightArr.Length ==> (forall idx :: l <= idx < k ==> a[idx] <= rightArr[j])
    invariant sorted(leftArr[..])
    decreases leftArr.Length - i
  {
    a[k] := leftArr[i];
    assert k == l ==> |a[l..k]| == 0;
    assert k > l ==> a[l..k][|a[l..k]|-1] == a[k-1];
    if k > l {
      assert j < rightArr.Length ==> a[k-1] <= rightArr[j];
      assert a[k-1] <= leftArr[i];
    }
    sortedExtend(a[l..k], leftArr[i]);
    i := i + 1;
    k := k + 1;
  }
  
  while j < rightArr.Length
    invariant 0 <= i <= leftArr.Length
    invariant 0 <= j <= rightArr.Length
    invariant l <= k <= r
    invariant k == l + i + j
    invariant leftArr[..] == old(a[l..m])
    invariant rightArr[..] == old(a[m..r])
    invariant a[..l] == old(a[..l])
    invariant a[r..] == old(a[r..])
    invariant sorted(a[l..k])
    invariant i < leftArr.Length ==> (forall idx :: l <= idx < k ==> a[idx] <= leftArr[i])
    invariant sorted(rightArr[..])
    decreases rightArr.Length - j
  {
    a[k] := rightArr[j];
    assert k == l ==> |a[l..k]| == 0;
    assert k > l ==> a[l..k][|a[l..k]|-1] == a[k-1];
    if k > l {
      assert i < leftArr.Length ==> a[k-1] <= leftArr[i];
      assert a[k-1] <= rightArr[j];
    }
    sortedExtend(a[l..k], rightArr[j]);
    j := j + 1;
    k := k + 1;
  }
}
// </vc-code>

// Ex3