method smallest_change(s: seq<int>) returns (c: int)
  // post-conditions-start
  ensures c == |set i | 0 <= i < |s| / 2 && s[i] != s[|s| - 1 - i]|
  // post-conditions-end
{
  // impl-start
  ghost var pos := {};
  c := 0;

  var i := 0;
  while i < |s| / 2
    // invariants-start
    invariant 0 <= i <= |s| / 2
    invariant pos == set j {:trigger s[j]} | 0 <= j < i && s[j] != s[|s| - 1 - j]
    invariant c == |pos|
    // invariants-end
  {
    if s[i] != s[|s| - 1 - i] {
      pos := pos + {i};
      c := c + 1;
    }
    i := i + 1;
  }
  // impl-end
}
