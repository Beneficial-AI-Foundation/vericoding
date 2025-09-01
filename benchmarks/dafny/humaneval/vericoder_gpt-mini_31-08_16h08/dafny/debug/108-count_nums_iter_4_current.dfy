

// <vc-helpers>
function prefix_count(s: seq<int>, n: nat): nat
  requires n <= |s|
{
  if n == 0 then 0 else prefix_count(s, n-1) + (if digits_sum(s[n-1]) > 0 then 1 else 0)
}

lemma count_prefix_eq_card(s: seq<int>, n: nat)
  requires n <= |s|
  ensures prefix_count(s,n) == |set j | 0 <= j < n && digits_sum(s[j]) > 0|
{
  if n == 0 {
    assert prefix_count(s,0) == 0;
    assert |set j | 0 <= j < 0 && digits_sum(s[j]) > 0| == 0;
  } else {
    count_prefix_eq_card(s, n-1);
    var A := set j | 0 <= j < n-1 && digits_sum(s[j]) > 0;
    if digits_sum(s[n-1]) > 0 {
      // larger set is A + {n-1}
      assert (set j | 0 <= j < n && digits_sum(s[j]) > 0) == A + {n-1};
      // A and {n-1} are disjoint
      assert forall k :: k in A ==> k != n-1;
      assert (A * {n-1}) == {};
      // cardinality of union of disjoint finite sets
      assert |A + {n-1}| == |A| + |{n-1}|;
      assert |{n-1}| == 1;
      assert |A + {n-1}| == |A| + 1;
      assert prefix_count(s,n) == prefix_count(s,n-1) + 1;
      assert prefix_count(s,n-1) == |A|;
      assert prefix_count(s,n) == |A| + 1;
      assert prefix_count(s,n) == |set j | 0 <= j < n && digits_sum(s[j]) > 0|;
    } else {
      // larger set equals A
      assert (set j | 0 <= j < n && digits_sum(s[j]) > 0) == A;
      assert prefix_count(s,n) == prefix_count(s,n-1);
      assert prefix_count(s,n-1) == |A|;
      assert prefix_count(s,n) == |A|;
      assert prefix_count(s,n) == |set j | 0 <= j < n && digits_sum(s[j]) > 0|;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method count_nums(s: seq<int>) returns (cnt: nat)
  // post-conditions-start
  ensures cnt == |set i | 0 <= i < |s| && digits_sum(s[i]) > 0|
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  cnt := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant 0 <= cnt <= i
    invariant cnt == prefix_count(s, i)
  {
    if digits_sum(s[i]) > 0 {
      cnt := cnt + 1;
    }
    i := i + 1;
  }
  count_prefix_eq_card(s, |s|);
  assert cnt == |set j | 0 <= j < |s| && digits_sum(s[j]) > 0|;
}
// </vc-code>

function digits_sum(x: int): int
  decreases abs(x)
{
  if abs(x) < 10 then x else x % 10 + digits_sum(x / 10)
}
// pure-end
function abs(x: int): int
  ensures abs(x) >= 0
  ensures abs(x) == x || abs(x) == -x
{
  if x >= 0 then x else -x
}
// pure-end