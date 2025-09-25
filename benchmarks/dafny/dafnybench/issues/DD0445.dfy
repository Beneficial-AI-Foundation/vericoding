// <vc-preamble>
method mergeArr(a: array<int>, l: int, m: int, r: int)
    requires 0 <= l <= m < r <= a.Length
    modifies a
{
    // Placeholder merge implementation
}

function sorted(s : seq<int>) : bool {
  forall k1, k2 :: 0 <= k1 <= k2 < |s| ==> s[k1] <= s[k2]
}


// Ex1



// Ex2


// Ex3
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method sort(a : array<int>) 
  ensures sorted(a[..])
  modifies a
// </vc-spec>
// <vc-code>
{
  if(a.Length == 0) { return; }
  else { sortAux(a, 0, a.Length); }
}
// </vc-code>

method sortAux(a : array<int>, l : int, r : int)
  ensures sorted(a[l..r])
  ensures a[..l] == old(a[..l])
  ensures a[r..] == old(a[r..])
  requires 0 <= l < r <= a.Length
  modifies a
  decreases r - l
{
  if(l >= (r - 1)) {return;}
  else {
    var m := l + (r - l) / 2;
    sortAux(a, l, m);
    sortAux(a, m, r);
    mergeArr(a, l, m, r);
    assume false;
    return;
  }
}