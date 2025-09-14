// <vc-preamble>
predicate Sorted(a: string, low:int, high:int)
requires 0 <= low <= high <= |a|
{ 
    forall j, k :: low <= j < k < high ==> a[j] <= a[k] 
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): created a helper method for sorting */
method Sort3Helper(c0: char, c1: char, c2: char) returns (s: seq<char>)
  ensures |s| == 3
  ensures s[0] <= s[1] && s[1] <= s[2]
  ensures multiset(s) == multiset{c0, c1, c2}
{
  var x, y, z := c0, c1, c2;
  if x > y { x, y := y, x; }
  if y > z { y, z := z, y; }
  if x > y { x, y := y, x; }
  s := [x, y, z];
}
// </vc-helpers>

// <vc-spec>
method String3Sort(a: string) returns (b: string) 
requires |a| == 3;
ensures Sorted(b, 0, |b|);
ensures |a| == |b|;
ensures multiset{b[0], b[1], b[2]} == multiset{a[0], a[1], a[2]};
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): called the sorting helper method */
  b := Sort3Helper(a[0], a[1], a[2]);
}
// </vc-code>
