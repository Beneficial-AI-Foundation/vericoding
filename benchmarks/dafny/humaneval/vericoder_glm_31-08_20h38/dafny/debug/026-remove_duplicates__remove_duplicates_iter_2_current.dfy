function count_rec(a: seq<int>, x: int): int {
  if |a| == 0 then 0
  else count_rec(a[1..], x) + (if a[0] == x then 1 else 0)
}

// <vc-helpers>
function count_rec(a: seq<int>, x: int): int {
  if |a| == 0 then 0
  else count_rec(a[1..], x) + (if a[0] == x then 1 else 0)
}

lemma count_rec_properties(a: seq<int>, x: int)
  ensures count_rec(a, x) == |set i | 0 <= i < |a| && a[i] == x|
{
  if |a| == 0 {
  } else {
    count_rec_properties(a[1..], x);
    calc {
      count_rec(a, x);
      count_rec(a[1..], x) + (if a[0] == x then 1 else 0);
      |set i | 0 <= i < |a[1..]| && a[1..][i] == x| + (if a[0] == x then 1 else 0);
      |set i | 0 <= i < |a[1..]| && a[i+1] == x| + (if a[0] == x then 1 else 0);
      { assert set j | 0 <= j < |a| && a[j] == x ==
          (if a[0] == x then {0} else {}) + 
          set j | 0 < j < |a| && a[j] == x; }
      |set i | 0 <= i < |a| && a[i] == x|;
    }
  }
}

lemma count_rec_monotonic(a: seq<int>, x: int, n: nat)
  requires n <= |a|
  ensures count_rec(a[..n], x) <= count_rec(a, x)
  decreases |a| - n
{
  if n == 0 {
  } else if n < |a| {
    count_rec_monotonic(a[1..], x, n-1);
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
    invariant forall j :: 0 <= j < i ==> (a[j] in result) == (count_rec(a, a[j]) == 1)
  {
    if count_rec(a, a[i]) == 1 {
      result := result + [a[i]];
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