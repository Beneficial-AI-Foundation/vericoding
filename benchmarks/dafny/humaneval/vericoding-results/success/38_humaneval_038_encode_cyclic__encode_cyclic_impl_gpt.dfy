// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): simple min helper retained */
function min(a: int, b: int): int {
  if a < b then a else b
}
// </vc-helpers>

// <vc-spec>
method encode_cyclic(s: seq<int>) returns (res: seq<int>) 

    ensures |s| == |res|
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 0 ==> res[i] == s[i + 1])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 1 ==> res[i] == s[i + 1])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 2 ==> res[i] == s[i - 2])
    ensures forall i :: |s| - |s| % 3 <= i < |s| ==> (res[i] == s[i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): construct result by iterating and building a rotated prefix and appending untouched tail */
  var n := |s|;
  var m := n % 3;
  var k := n - m;

  var r: seq<int> := [];
  var i: int := 0;

  assert k % 3 == 0;
  while i < k
    invariant 0 <= i <= k
    invariant |r| == i
    invariant forall j :: 0 <= j < i ==> (j % 3 == 0 ==> r[j] == s[j + 1])
    invariant forall j :: 0 <= j < i ==> (j % 3 == 1 ==> r[j] == s[j + 1])
    invariant forall j :: 0 <= j < i ==> (j % 3 == 2 ==> r[j] == s[j - 2])
  {
    if i % 3 != 2 {
      assert i + 1 <= k;
      assert k % 3 == 0;
      assert (i + 1) % 3 != 0;
      assert i + 1 < k;
      assert i + 1 < n;
    } else {
      assert i >= 2;
      assert i - 2 >= 0;
      assert i - 2 < n;
    }
    var v := if i % 3 != 2 then s[i + 1] else s[i - 2];
    r := r + [v];
    i := i + 1;
  }
  res := r + s[k..];
}
// </vc-code>
