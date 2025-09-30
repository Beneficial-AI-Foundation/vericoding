// <vc-preamble>

function count(s: seq<int>, x: int): int
{
    |set i | 0 <= i < |s| && s[i] == x|
}

function max_seq(s: seq<int>): int
    requires |s| > 0
    ensures forall i :: 0 <= i < |s| ==> s[i] <= max_seq(s)
    ensures max_seq(s) in s
{
    if |s| == 1 then s[0]
    else if s[0] >= max_seq(s[1..]) then s[0]
    else max_seq(s[1..])
}

predicate ValidInput(lst: seq<int>)
{
    |lst| > 0 && forall i :: 0 <= i < |lst| ==> lst[i] > 0
}

predicate ValidResult(lst: seq<int>, result: int)
    requires ValidInput(lst)
{
    var frequency := map x | x in lst :: x := count(lst, x);
    if result == -1 then
        forall x :: x in frequency ==> frequency[x] < x
    else
        result > 0 &&
        result in frequency && 
        frequency[result] >= result &&
        forall y :: y in frequency && frequency[y] >= y ==> y <= result
}
lemma count_append_lemma(s: seq<int>, elem: int, x: int)
    ensures count(s + [elem], x) == count(s, x) + (if x == elem then 1 else 0)
{
    var s' := s + [elem];
    var original_indices := set i | 0 <= i < |s| && s[i] == x;
    var new_indices := set i | 0 <= i < |s'| && s'[i] == x;

    assert forall i :: 0 <= i < |s| ==> s'[i] == s[i];
    assert original_indices == set i | 0 <= i < |s| && s'[i] == x;

    if x == elem {
        assert s'[|s|] == elem == x;
        assert new_indices == original_indices + {|s|};
        assert |s| !in original_indices;
        assert |new_indices| == |original_indices| + 1;
    } else {
        assert s'[|s|] == elem != x;
        assert new_indices == original_indices;
        assert |new_indices| == |original_indices|;
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): CountNonNeg proof */
lemma CountNonNeg(s: seq<int>, x: int)
  ensures count(s, x) >= 0
{
  assert count(s, x) >= 0;
}

/* helper modified by LLM (iteration 3): CountZeroIffNotIn proof by induction on length */
lemma CountZeroIffNotIn(s: seq<int>, x: int)
  ensures count(s, x) == 0 <==> (forall i :: 0 <= i < |s| ==> s[i] != x)
{
  if |s| == 0 {
    assert count(s, x) == 0;
    assert forall i :: 0 <= i < 0 ==> s[i] != x;
    return;
  }
  var s0 := s[..|s|-1];
  var elem := s[|s|-1];
  assert s == s0 + [elem];
  count_append_lemma(s0, elem, x);
  assert count(s, x) == count(s0, x) + (if x == elem then 1 else 0);

  // Forward: count(s,x) == 0 -> no index contains x
  if count(s, x) == 0 {
    if x == elem {
      // contradiction because then count(s,x) = count(s0,x) + 1 >=1
      CountNonNeg(s0, x);
      assert count(s0, x) + 1 > 0;
      assert false;
    } else {
      assert count(s0, x) == 0;
      CountZeroIffNotIn(s0, x);
      assert forall i :: 0 <= i < |s0| ==> s0[i] != x;
      assert elem != x;
      assert forall i :: 0 <= i < |s| ==> s[i] != x;
    }
  }

  // Backward: no index contains x -> count(s,x) == 0
  if forall i :: 0 <= i < |s| ==> s[i] != x {
    assert forall i :: 0 <= i < |s0| ==> s0[i] != x;
    assert elem != x;
    CountZeroIffNotIn(s0, x);
    assert count(s0, x) == 0;
    assert count(s, x) == 0;
  }
}

// </vc-helpers>

// <vc-spec>
method search(lst: seq<int>) returns (result: int)
    requires ValidInput(lst)
    ensures ValidResult(lst, result)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): implement search scanning with invariants */
  var i := 0;
  var best := -1;
  while i < |lst|
    invariant 0 <= i <= |lst|
    invariant forall j :: 0 <= j < i ==> (count(lst, lst[j]) >= lst[j] ==> lst[j] <= best)
    invariant (best == -1) || (exists k :: 0 <= k < i && lst[k] == best && count(lst, best) >= best)
  {
    var v := lst[i];
    var c := count(lst, v);
    if c >= v && v > best {
      best := v;
    }
    i := i + 1;
  }
  result := best;
  if result == -1 {
    // then for all elements of lst, count < element
    assert forall j :: 0 <= j < |lst| ==> count(lst, lst[j]) < lst[j];
    assert forall x :: x in lst ==> count(lst, x) < x;
  } else {
    assert result in lst;
    assert count(lst, result) >= result;
    assert forall j :: 0 <= j < |lst| ==> (count(lst, lst[j]) >= lst[j] ==> lst[j] <= result);
    assert forall y :: y in lst && count(lst, y) >= y ==> y <= result;
  }
}

// </vc-code>
