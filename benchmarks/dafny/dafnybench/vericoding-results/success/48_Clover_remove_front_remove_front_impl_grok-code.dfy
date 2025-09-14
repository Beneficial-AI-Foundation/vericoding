

// <vc-helpers>
//
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method remove_front(a:array<int>) returns (c:array<int>)
  requires a.Length>0
  ensures  a[1..] == c[..]
// </vc-spec>
// <vc-code>
{ 
  var len := a.Length - 1;
  c := new int[len];
  var i := 0;
  while i < len 
    invariant 0 <= i <= len
    invariant forall j :: 0 <= j < i ==> c[j] == a[j+1]
  {
    c[i] := a[i+1];
    i := i + 1;
  }
}
// </vc-code>

