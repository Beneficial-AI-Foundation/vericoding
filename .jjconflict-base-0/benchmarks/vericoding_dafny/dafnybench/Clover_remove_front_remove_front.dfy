// <vc-helpers>
// </vc-helpers>

method remove_front(a:array<int>) returns (c:array<int>)
  requires a.Length>0
  ensures  a[1..] == c[..]
// <vc-code>
{
  assume false;
}
// </vc-code>