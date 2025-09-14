

// <vc-helpers>
lemma set_cardinal_succ(s: seq<int>, i: int)
  requires 0 <= i < |s|
  ensures |set j | 0 <= j < i+1 && digits_sum(s[j]) > 0| ==
          |set j | 0 <= j < i && digits_sum(s[j]) > 0| + (if digits_sum(s[i]) > 0 then 1 else 0)
{
  var A := set j | 0 <= j < i && digits_sum(s[j]) > 0;
  // membership facts about A
  assert forall k :: k in A ==> 0 <= k < i && digits_sum(s[k]) > 0;

  if digits_sum(s[i]) > 0 {
    // then the i-th element belongs to the larger set
    assert i in (set j | 0 <= j < i+1 && digits_sum(s[j]) > 0);
    // show the larger set equals A + {i}
    assert (set j | 0 <= j < i+1 && digits_sum(s[j]) > 0) == A + {i};
    // A and {i} are disjoint because every element of A is < i
    assert forall k :: k in A ==> k != i;
    assert (A * {i}) == {};
    assert |A + {i}| == |A| + |{i}|;
    assert |{i}| == 1;
    assert |A + {i}| == |A| + 1;
    assert |set j | 0 <= j < i+1 && digits_sum(s[j]) > 0| == |A| + 1;
  } else {
    // i-th element is not in the larger set, so larger set equals A
    assert (set j | 0 <= j < i+1 && digits_sum(s[j]) > 0) == A;
    assert |set j | 0 <= j < i+1 && digits_sum(s[j]) > 0| == |A|;
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
    invariant 0 <= cnt <= |s|
    invariant cnt == |set j | 0 <= j < i && digits_sum(s[j]) > 0|
  {
    // Relate cardinalities of prefix sets for i and i+1
    set_cardinal_succ(s, i);
    if digits_sum(s[i]) > 0 {
      // increment count to reflect inclusion of index i
      cnt := cnt + 1;
      // now cnt should equal the cardinality for prefix length i+1
      assert cnt == |set j | 0 <= j < i+1 && digits_sum(s[j]) > 0|;
    } else {
      // cnt already equals the cardinality for prefix length i+1 (unchanged)
      assert cnt == |set j | 0 <= j < i+1 && digits_sum(s[j]) > 0|;
    }
    i := i + 1;
  }
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