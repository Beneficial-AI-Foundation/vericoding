predicate ValidInput(n: int, m: int, k: int, emotes: seq<int>)
{
    n >= 2 && k >= 1 && m >= 1 && |emotes| == n &&
    forall i :: 0 <= i < |emotes| ==> emotes[i] >= 1
}

function MaxHappiness(n: int, m: int, k: int, emotes: seq<int>): int
    requires ValidInput(n, m, k, emotes)
{
    var k_plus_1 := k + 1;
    var total := m / k_plus_1;
    var remainder := m % k_plus_1;
    // Assumes optimal strategy using highest and second highest values
    var max_val := MaxValue(emotes);
    var second_max_val := SecondMaxValue(emotes);
    remainder * max_val + max_val * (total * k) + second_max_val * total
}

function MaxValue(s: seq<int>): int
    requires |s| >= 1
    requires forall i :: 0 <= i < |s| ==> s[i] >= 1
    ensures MaxValue(s) >= 1
    ensures exists i :: 0 <= i < |s| && s[i] == MaxValue(s)
{
    if |s| == 1 then s[0]
    else if s[0] >= MaxValue(s[1..]) then s[0]
    else MaxValue(s[1..])
}

function SecondMaxValue(s: seq<int>): int
    requires |s| >= 2
    requires forall i :: 0 <= i < |s| ==> s[i] >= 1
{
    var max_val := MaxValue(s);
    var filtered := FilterOut(s, max_val, 1);
    if |filtered| > 0 then MaxValue(filtered) else 1
}

function FilterOut(s: seq<int>, val: int, count: int): seq<int>
    requires count >= 0
    requires forall i :: 0 <= i < |s| ==> s[i] >= 1
    ensures forall i :: 0 <= i < |FilterOut(s, val, count)| ==> FilterOut(s, val, count)[i] >= 1
{
    if |s| == 0 || count == 0 then s
    else if s[0] == val then FilterOut(s[1..], val, count - 1)
    else [s[0]] + FilterOut(s[1..], val, count)
}

// <vc-helpers>
lemma MaxValueLemma(s: seq<int>, i: int)
  requires |s| >= 1
  requires forall j :: 0 <= j < |s| ==> s[j] >= 1
  requires 0 <= i < |s|
  ensures s[i] <= MaxValue(s)
{
  if |s| == 1 {
    // Trivial case: single element
  } else {
    if i == 0 {
      if s[0] >= MaxValue(s[1..]) {
        // s[0] is the maximum
      } else {
        assert MaxValue(s) == MaxValue(s[1..]);
        MaxValueLemma(s[1..], 0);
        assert s[0] <= MaxValue(s[1..]);
      }
    } else {
      MaxValueLemma(s[1..], i-1);
      assert s[i] <= MaxValue(s[1..]);
      if s[0] >= MaxValue(s[1..]) {
        assert MaxValue(s) == s[0];
      } else {
        assert MaxValue(s) == MaxValue(s[1..]);
      }
    }
  }
}

lemma SecondMaxValueLemma(s: seq<int>)
  requires |s| >= 2
  requires forall i :: 0 <= i < |s| ==> s[i] >= 1
  ensures SecondMaxValue(s) <= MaxValue(s)
  ensures exists i :: 0 <= i < |s| && s[i] == SecondMaxValue(s) && s[i] <= MaxValue(s)
{
  var max_val := MaxValue(s);
  var filtered := FilterOut(s, max_val, 1);
  if |filtered| > 0 {
    MaxValueLemma(filtered, 0);
    assert MaxValue(filtered) <= max_val;
  }
}

lemma FilterOutMaintainsPositive(s: seq<int>, val: int, count: int)
  requires count >= 0
  requires forall i :: 0 <= i < |s| ==> s[i] >= 1
  ensures forall i :: 0 <= i < |FilterOut(s, val, count)| ==> FilterOut(s, val, count)[i] >= 1
{
  if |s| == 0 || count == 0 {
  } else {
    if s[0] == val {
      FilterOutMaintainsPositive(s[1..], val, count - 1);
    } else {
      FilterOutMaintainsPositive(s[1..], val, count);
    }
  }
}

lemma FilterOutMaxValueLemma(s: seq<int>, val: int, count: int)
  requires count >= 0
  requires |s| >= 1
  requires forall i :: 0 <= i < |s| ==> s[i] >= 1
  requires val >= 1
  ensures forall x :: x in FilterOut(s, val, count) ==> x <= MaxValue(s)
{
  if |s| == 0 || count == 0 {
  } else {
    if s[0] == val {
      FilterOutMaxValueLemma(s[1..], val, count - 1);
    } else {
      FilterOutMaxValueLemma(s[1..], val, count);
      MaxValueLemma(s, 0);
    }
  }
}

lemma FilterOutContainsLemma(s: seq<int>, val: int, count: int)
  requires count >= 0
  requires forall i :: 0 <= i < |s| ==> s[i] >= 1
  requires val >= 1
  ensures forall x :: x in s && (x != val || count == 0) ==> x in FilterOut(s, val, count)
{
  if |s| == 0 || count == 0 {
  } else {
    if s[0] == val {
      FilterOutContainsLemma(s[1..], val, count - 1);
    } else {
      FilterOutContainsLemma(s[1..], val, count);
    }
  }
}

lemma FilterOutMaxValueLemmaComplete(s: seq<int>, val: int, count: int)
  requires count >= 0
  requires |s| >= 1
  requires forall i :: 0 <= i < |s| ==> s[i] >= 1
  requires val >= 1
  ensures MaxValue(FilterOut(s, val, count)) <= MaxValue(s)
{
  if |s| == 0 || count == 0 {
  } else {
    if s[0] == val {
      FilterOutMaxValueLemmaComplete(s[1..], val, count - 1);
    } else {
      FilterOutMaxValueLemmaComplete(s[1..], val, count);
      MaxValueLemma(s, 0);
    }
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, k: int, emotes: seq<int>) returns (result: int)
    requires ValidInput(n, m, k, emotes)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
  var k_plus_1 := k + 1;
  var total := m / k_plus_1;
  var remainder := m % k_plus_1;
  var max_val := MaxValue(emotes);
  var second_max_val := SecondMaxValue(emotes);
  
  SecondMaxValueLemma(emotes);
  assert second_max_val <= max_val;
  
  assert m >= 0;
  assert k_plus_1 > 0;
  assert total >= 0;
  assert remainder >= 0;
  assert max_val >= 1;
  assert second_max_val >= 1;
  
  var filtered := FilterOut(emotes, max_val, 1);
  if |filtered| > 0 {
    FilterOutMaxValueLemmaComplete(emotes, max_val, 1);
    assert MaxValue(filtered) <= max_val;
  } else {
    assert second_max_val == 1;
    assert 1 <= max_val;
  }
  
  result := remainder * max_val + max_val * (total * k) + second_max_val * total;
  assert result >= 0;
}
// </vc-code>

