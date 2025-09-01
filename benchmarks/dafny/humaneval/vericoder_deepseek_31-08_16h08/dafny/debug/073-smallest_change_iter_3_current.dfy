

// <vc-helpers>
lemma CountLemma(s: seq<int>, low: int, high: int, count: int)
  requires 0 <= low <= high <= |s|
  ensures |set i | low <= i < high && s[i] != s[|s| - 1 - i]| == count
  decreases high - low
{
  if low < high {
    var next := low + 1;
    if s[low] != s[|s| - 1 - low] {
      CountLemma(s, next, high, count + 1);
    } else {
      CountLemma(s, next, high, count);
    }
  }
}

lemma CountLemmaExtension(s: seq<int>, i: int, n: int, c: int)
  requires 0 <= i <= n / 2
  requires n == |s|
  requires c == |set j | 0 <= j < i && s[j] != s[n - 1 - j]|
  ensures |set j | 0 <= j < n / 2 && s[j] != s[n - 1 - j]| == c + |set j | i <= j < n / 2 && s[j] != s[n - 1 - j]|
{
  CountLemma(s, i, n / 2, |set j | i <= j < n / 2 && s[j] != s[n - 1 - j]|);
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method smallest_change(s: seq<int>) returns (c: int)
  // post-conditions-start
  ensures c == |set i | 0 <= i < |s| / 2 && s[i] != s[|s| - 1 - i]|
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var n := |s|;
  c := 0;
  var i := 0;
  while i < n / 2
    invariant 0 <= i <= n / 2
    invariant c == |set j | 0 <= j < i && s[j] != s[n - 1 - j]|
  {
    if s[i] != s[n - 1 - i] {
      c := c + 1;
    }
    i := i + 1;
  }
  CountLemmaExtension(s, i, n, c);
}
// </vc-code>

