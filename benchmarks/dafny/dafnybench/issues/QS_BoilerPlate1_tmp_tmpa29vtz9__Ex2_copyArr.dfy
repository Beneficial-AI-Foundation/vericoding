// <vc-preamble>
function sorted(s : seq<int>) : bool {
  forall k1, k2 :: 0 <= k1 <= k2 < |s| ==> s[k1] <= s[k2]
}


// Ex1
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method copyArr(a : array<int>, l : int, r : int) returns (ret : array<int>)
  requires 0 <= l < r <= a.Length 
  ensures ret[..] == a[l..r]
// </vc-spec>
// <vc-code>
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
// </vc-code>

// Ex2


// Ex3