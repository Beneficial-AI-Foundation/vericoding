function count_rec(a: seq<int>, x: int): int {
  if |a| == 0 then 0
  else count_rec(a[1..], x) + (if a[0] == x then 1 else 0)
}

// <vc-helpers>
lemma count_rec_split(a: seq<int>, x: int, i: int)
  requires 0 <= i <= |a|
  ensures count_rec(a, x) == count_rec(a[..i], x) + count_rec(a[i..], x)
{
  if i == 0 {
    assert a[..i] == [];
    assert a[i..] == a;
  } else if i == |a| {
    assert a[..i] == a;
    assert a[i..] == [];
  } else {
    if |a| > 0 && i > 0 {
      count_rec_split(a[1..], x, i-1);
    }
  }
}

lemma count_rec_append(a: seq<int>, b: seq<int>, x: int)
  ensures count_rec(a + b, x) == count_rec(a, x) + count_rec(b, x)
{
  if |a| == 0 {
    assert a + b == b;
  } else {
    count_rec_append(a[1..], b, x);
    assert (a + b)[1..] == a[1..] + b;
  }
}

lemma count_rec_single(elem: int, x: int)
  ensures count_rec([elem], x) == if elem == x then 1 else 0
{
}

lemma count_rec_not_in(a: seq<int>, x: int)
  requires x !in a
  ensures count_rec(a, x) == 0
{
  if |a| == 0 {
  } else {
    assert a[0] != x;
    count_rec_not_in(a[1..], x);
  }
}
// </vc-helpers>

// <vc-spec>
method remove_duplicates(a: seq<int>) returns (result: seq<int>)
  // pre-conditions-start
  requires forall i :: 0 <= i < |a| ==> count_rec(a, a[i]) >= 1
  // pre-conditions-end
  // post-conditions-start
  ensures forall i :: 0 <= i < |result| ==> count_rec(a, result[i]) == 1
  ensures forall i :: 0 <= i < |a| ==> (a[i] in result <==> count_rec(a, a[i]) == 1)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  result := [];
  var i := 0;
  
  while i < |a|
    invariant 0 <= i <= |a|
    invariant forall j :: 0 <= j < |result| ==> count_rec(a, result[j]) == 1
    invariant forall j :: 0 <= j < i ==> (a[j] in result <==> count_rec(a, a[j]) == 1)
    invariant forall j :: 0 <= j < |result| ==> exists k :: 0 <= k < i && result[j] == a[k]
  {
    var cnt := count(a, a[i]);
    
    if cnt == 1 && a[i] !in result {
      result := result + [a[i]];
      
      // Prove that a[i] is not already in result
      forall j | 0 <= j < |result| - 1
        ensures result[j] != a[i]
      {
        if result[j] == a[i] {
          var k :| 0 <= k < i && result[j] == a[k];
          assert a[k] == a[i];
          assert count_rec(a, a[k]) == 1;
          assert count_rec(a, a[i]) == 1;
          assert false;
        }
      }
    }
    
    i := i + 1;
  }
}
// </vc-code>

method count(a: seq<int>, x: int) returns (cnt: int)
  // post-conditions-start
  ensures cnt == |set i | 0 <= i < |a| && a[i] == x|
  ensures cnt == count_rec(a, x)
  // post-conditions-end
{
  assume{:axiom} false;
}