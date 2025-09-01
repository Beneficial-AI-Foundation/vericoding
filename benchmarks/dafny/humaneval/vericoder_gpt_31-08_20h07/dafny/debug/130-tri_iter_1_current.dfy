function tri(n: nat): nat
  decreases if n % 2 == 0 then 0 else n
{
  if n == 1 then 3
  else if n % 2 == 0 then 1 + n / 2
  else tri(n - 1) + tri(n - 2) + tri(n + 1)
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Tribonacci(n: nat) returns (result: seq<nat>)
  // post-conditions-start
  ensures |result| == n + 1
  ensures forall i :: 0 <= i <= n ==> result[i] == tri(i)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var r: seq<nat> := [];
  var i: nat := 0;
  while i <= n
    invariant |r| == i
    invariant i <= n + 1
    invariant forall j :: 0 <= j < i ==> r[j] == tri(j)
    decreases n - i + 1
  {
    var v: nat;
    if i == 0 {
      v := 1 + i / 2;
      assert i % 2 == 0;
      assert tri(i) == 1 + i / 2;
    } else if i == 1 {
      v := 3;
      assert tri(i) == 3;
    } else if i % 2 == 0 {
      v := 1 + i / 2;
      assert tri(i) == 1 + i / 2;
    } else {
      assert i >= 3;
      assert i - 1 >= 0 && i - 2 >= 0;
      assert (i + 1) % 2 == 0;
      var tNext: nat := 1 + (i + 1) / 2;
      v := r[i - 1] + r[i - 2] + tNext;
      assert tri(i) == tri(i - 1) + tri(i - 2) + tri(i + 1);
      assert tri(i + 1) == tNext;
      assert r[i - 1] == tri(i - 1);
      assert r[i - 2] == tri(i - 2);
      assert v == tri(i);
    }
    // for even/1/0 branches, v == tri(i) already asserted; make it explicit for all paths
    assert v == tri(i);
    r := r + [v];
    i := i + 1;
  }
  result := r;
}
// </vc-code>

