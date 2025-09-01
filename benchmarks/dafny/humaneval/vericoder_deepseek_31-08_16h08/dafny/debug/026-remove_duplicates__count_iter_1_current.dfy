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
lemma CountRecMatch(a: seq<int>, x: int)
  ensures count_rec(a, x) == |set i | 0 <= i < |a| && a[i] == x|
{
  if |a| == 0 {
    // Base case: empty sequence
    assert set i | 0 <= i < |a| && a[i] == x == {};
    assert |set i | 0 <= i < |a| && a[i] == x| == 0;
  } else {
    // Recursive case
    var head := a[0];
    var tail := a[1..];
    
    // Recursive call
    CountRecMatch(tail, x);
    
    if head == x {
      // If head matches, add 1 to count
      assert set i | 0 <= i < |a| && a[i] == x == 
        {0} ∪ {i+1 | i in set j | 0 <= j < |tail| && tail[j] == x};
      assert |set i | 0 <= i < |a| && a[i] == x| == 
        |set j | 0 <= j < |tail| && tail[j] == x| + 1;
    } else {
      // If head doesn't match, count remains same
      assert set i | 0 <= i < |a| && a[i] == x == 
        {i+1 | i in set j | 0 <= j < |tail| && tail[j] == x};
      assert |set i | 0 <= i < |a| && a[i] == x| == 
        |set j | 0 <= j < |tail| && tail[j] == x|;
    }
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
    invariant cnt == |set j | 0 <= j < i && a[j] == x|
  {
    if a[i] == x {
      cnt := cnt + 1;
    }
    i := i + 1;
  }
  
  CountRecMatch(a, x);
}
// </vc-code>

