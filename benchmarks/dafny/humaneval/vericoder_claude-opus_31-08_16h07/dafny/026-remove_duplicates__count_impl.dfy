function count_rec(a: seq<int>, x: int): int {
  if |a| == 0 then 0
  else count_rec(a[1..], x) + (if a[0] == x then 1 else 0)
}
method remove_duplicates(a: seq<int>) returns (result: seq<int>)
  // pre-conditions-start
  requires forall i :: 0 <= i < |a| ==> count_rec(a, a[i]) >= 1
  // pre-conditions-end
  // post-conditions-start
  ensures forall i :: 0 <= i < |result| ==> count_rec(a, result[i]) == 1
  ensures forall i :: 0 <= i < |a| ==> (a[i] in result <==> count_rec(a, a[i]) == 1)
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma count_rec_split(a: seq<int>, x: int, k: int)
  requires 0 <= k <= |a|
  ensures count_rec(a, x) == count_rec(a[..k], x) + count_rec(a[k..], x)
{
  if k == 0 {
    assert a[..0] == [];
    assert a[0..] == a;
  } else {
    count_rec_split(a[1..], x, k-1);
    assert a[1..][..k-1] == a[..k][1..];
    assert a[1..][k-1..] == a[k..];
  }
}

lemma count_rec_append(a: seq<int>, x: int, y: int)
  ensures count_rec(a + [y], x) == count_rec(a, x) + (if y == x then 1 else 0)
{
  if |a| == 0 {
    assert a + [y] == [y];
  } else {
    count_rec_append(a[1..], x, y);
    assert (a + [y])[1..] == a[1..] + [y];
  }
}
// </vc-helpers>

// <vc-spec>
method count(a: seq<int>, x: int) returns (cnt: int)
  // post-conditions-start
  ensures cnt == |set i | 0 <= i < |a| && a[i] == x|
  ensures cnt == count_rec(a, x)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  cnt := 0;
  var i := 0;
  
  while i < |a|
    invariant 0 <= i <= |a|
    invariant cnt == count_rec(a[..i], x)
    invariant cnt == |set j | 0 <= j < i && a[j] == x|
  {
    var old_cnt := cnt;
    if a[i] == x {
      cnt := cnt + 1;
    }
    
    // Prove the set invariant
    var S_old := set j | 0 <= j < i && a[j] == x;
    var S_new := set j | 0 <= j < i + 1 && a[j] == x;
    
    if a[i] == x {
      assert S_new == S_old + {i};
      assert |S_new| == |S_old| + 1;
    } else {
      assert S_new == S_old;
    }
    
    // Prove the count_rec invariant
    assert a[..i+1] == a[..i] + [a[i]];
    count_rec_append(a[..i], x, a[i]);
    
    i := i + 1;
  }
  
  assert a[..i] == a;
}
// </vc-code>

