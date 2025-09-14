// <vc-preamble>
function count_rec(a: seq<int>, x: int): int {
  if |a| == 0 then 0
  else count_rec(a[1..], x) + (if a[0] == x then 1 else 0)
}
// </vc-preamble>

// <vc-helpers>
lemma lemma_count_rec_append(s: seq<int>, y: int, x: int)
  ensures count_rec(s + [y], x) == count_rec(s, x) + (if y == x then 1 else 0)
  decreases s
{
  if |s| > 0 {
    lemma_count_rec_append(s[1..], y, x);
  }
}
// </vc-helpers>

// <vc-spec>
method count(a: seq<int>, x: int) returns (cnt: int)

  ensures cnt == |set i | 0 <= i < |a| && a[i] == x|
  ensures cnt == count_rec(a, x)
// </vc-spec>
// <vc-code>
{
  cnt := 0;
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant cnt == |set j | 0 <= j < i && a[j] == x|
    invariant cnt == count_rec(a[..i], x)
  {
    lemma_count_rec_append(a[..i], a[i], x);
    if a[i] == x {
      cnt := cnt + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
