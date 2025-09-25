// <vc-preamble>
function sorted(s : seq<int>) : bool {
  forall k1, k2 :: 0 <= k1 <= k2 < |s| ==> s[k1] <= s[k2]
}


// Ex1

method copyArr(a : array<int>, l : int, r : int) returns (ret : array<int>)
  requires 0 <= l < r <= a.Length 
  ensures ret[..] == a[l..r]
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
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
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
  var left := copyArr(a, l, m);
  var right := copyArr(a, m, r);
  var i := 0;
  var j := 0;
  var cur := l;
  ghost var old_arr := a[..];
  while(cur < r) 
    decreases a.Length - cur
    invariant 0 <= i <= left.Length
    invariant 0 <= j <= right.Length
    invariant l <= cur <= r
    invariant cur == i + j + l
    invariant a[..l] == old_arr[..l]
    invariant a[r..] == old_arr[r..]
    invariant sorted(a[l..cur])
    invariant sorted(left[..])
    invariant sorted(right[..])
    invariant i < left.Length && cur > l ==> a[cur - 1] <= left[i] 
    invariant j < right.Length && cur > l ==> a[cur - 1] <= right[j]
  {
    if((i == left.Length && j < right.Length) || (j != right.Length && left[i] > right[j])) {
      a[cur] := right[j];
      j := j + 1;
    }
    else if((j == right.Length && i < left.Length) || (i != left.Length && left[i] <= right[j])) {
      a[cur] := left[i];
      i := i + 1;
    }
    cur := cur + 1;
  }
  return;
}
// </vc-code>

// Ex3