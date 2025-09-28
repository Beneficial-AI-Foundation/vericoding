// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): define ShiftDown with nat-safe decrement using 'as nat' */
function ShiftDown(s: seq<nat>): seq<nat>
  decreases |s|
{
  if |s| == 0 then s
  else [(if s[0] == 0 then 0 else (s[0] - 1) as nat)] + ShiftDown(s[1..])
}

/* helper modified by LLM (iteration 5): length preservation of ShiftDown */
lemma ShiftDownLength(s: seq<nat>)
  ensures |ShiftDown(s)| == |s|
  decreases |s|
{
  if |s| == 0 {
  } else {
    ShiftDownLength(s[1..]);
    assert ShiftDown(s) == [(if s[0] == 0 then 0 else (s[0] - 1) as nat)] + ShiftDown(s[1..]);
  }
}

/* helper modified by LLM (iteration 5): element-wise behavior of ShiftDown */
lemma ShiftDownAt(s: seq<nat>, k: int)
  requires 0 <= k < |s|
  ensures ShiftDown(s)[k] == (if s[k] == 0 then 0 else (s[k] - 1) as nat)
  decreases |s|
{
  if k == 0 {
    assert ShiftDown(s) == [(if s[0] == 0 then 0 else (s[0] - 1) as nat)] + ShiftDown(s[1..]);
    assert ShiftDown(s)[0] == (if s[0] == 0 then 0 else (s[0] - 1) as nat);
  } else {
    ShiftDownLength(s[1..]);
    ShiftDownAt(s[1..], k - 1);
    assert ShiftDown(s) == [(if s[0] == 0 then 0 else (s[0] - 1) as nat)] + ShiftDown(s[1..]);
    assert ShiftDown(s)[k] == ShiftDown(s[1..])[k - 1];
    assert s[1..][k - 1] == s[k];
  }
}

/* helper modified by LLM (iteration 5): prove ShiftDown(l[1..]) is strictly increasing when l starts with 0 and is strictly increasing */
lemma StrictlyIncreasingShiftDownTail(l: seq<nat>)
  requires forall i, j :: 0 <= i < j < |l| ==> l[i] < l[j]
  requires 0 < |l|
  requires l[0] == 0
  ensures forall i, j :: 0 <= i < j < |l| - 1 ==> ShiftDown(l[1..])[i] < ShiftDown(l[1..])[j]
{
  var t := l[1..];
  var s := ShiftDown(t);
  // Each element of t is positive
  assert forall i :: 0 <= i < |t| ==> t[i] > 0 by {
    forall i | 0 <= i < |t| {
      assert 0 <= i + 1 < |l|;
      assert l[0] < l[i + 1];
      assert l[i + 1] > 0;
    }
  }
  // Show strict increase after shifting down
  forall i, j | 0 <= i < j < |t|
    ensures s[i] < s[j]
  {
    ShiftDownAt(t, i);
    ShiftDownAt(t, j);
    assert s[i] == (if t[i] == 0 then 0 else (t[i] - 1) as nat);
    assert s[j] == (if t[j] == 0 then 0 else (t[j] - 1) as nat);
    assert t[i] > 0;
    assert t[j] > 0;
    assert s[i] == (t[i] - 1) as nat && s[j] == (t[j] - 1) as nat;
    // inherit strictness from t
    assert t[i] < t[j];
    assert t[i] - 1 < t[j] - 1;
    assert 0 <= t[i] - 1 && 0 <= t[j] - 1;
    assert ((t[i] - 1) as nat) < ((t[j] - 1) as nat);
    assert s[i] < s[j];
  }
}

/* helper modified by LLM (iteration 5): relate membership of l and ShiftDown(l[1..]) for positive y */
lemma InShiftDownTailEquiv(l: seq<nat>, y: nat)
  requires forall i, j :: 0 <= i < j < |l| ==> l[i] < l[j]
  requires 0 < |l|
  requires l[0] == 0
  requires y > 0
  ensures (y in l) <==> (((y - 1) as nat) in ShiftDown(l[1..]))
{
  var t := l[1..];
  var s := ShiftDown(t);
  assert forall i :: 0 <= i < |t| ==> t[i] > 0 by {
    forall i | 0 <= i < |t| {
      assert 0 <= i + 1 < |l|;
      assert l[0] < l[i + 1];
      assert l[i + 1] > 0;
    }
  }
  if y in l {
    var k: int :| 0 <= k < |l| && l[k] == y;
    assert k != 0;
    assert 0 <= k - 1 < |t|;
    assert t[k - 1] == y;
    ShiftDownAt(t, k - 1);
    assert s[k - 1] == (y - 1) as nat;
    assert ((y - 1) as nat) in s;
  }
  if ((y - 1) as nat) in s {
    var i: int :| 0 <= i < |s| && s[i] == (y - 1) as nat;
    assert 0 <= i < |t|;
    ShiftDownAt(t, i);
    assert s[i] == (if t[i] == 0 then 0 else (t[i] - 1) as nat);
    assert t[i] > 0;
    assert s[i] == (t[i] - 1) as nat;
    assert t[i] == y;
    assert 0 <= i + 1 < |l|;
    assert l[i + 1] == y;
    assert y in l;
  }
}

/* helper modified by LLM (iteration 5): define SmallestMissing recursively using ShiftDown */
function SmallestMissing(l: seq<nat>): nat
  decreases |l|
{
  if |l| == 0 then 0
  else if l[0] == 0 then (1 + SmallestMissing(ShiftDown(l[1..]))) as nat
  else 0
}

/* helper modified by LLM (iteration 5): auxiliary lemma proving the spec by recursion on the sequence */
lemma SmallestMissingSpecSatisfiedAux(l: seq<nat>)
  requires forall i, j :: 0 <= i < j < |l| ==> l[i] < l[j]
  ensures SmallestMissing(l) !in l
  ensures forall candidate: nat :: candidate < SmallestMissing(l) ==> candidate in l
  decreases |l|
{
  if |l| == 0 {
    assert SmallestMissing(l) == 0;
    assert SmallestMissing(l) !in l;
  } else if l[0] > 0 {
    assert SmallestMissing(l) == 0;
    // show 0 !in l
    if 0 in l {
      var k: int :| 0 <= k < |l| && l[k] == 0;
      if k == 0 {
        assert l[0] > 0; // contradiction
      } else {
        assert l[0] < l[k];
        assert l[k] > 0; // contradiction with l[k] == 0
      }
    }
  } else {
    // l[0] == 0
    var t := l[1..];
    var s := ShiftDown(t);
    StrictlyIncreasingShiftDownTail(l);
    SmallestMissingSpecSatisfiedAux(s);
    var sm := SmallestMissing(s);
    assert SmallestMissing(l) == ((1 + sm) as nat);

    // smallest missing not in l
    InShiftDownTailEquiv(l, ((1 + sm) as nat));
    assert (((1 + sm) as nat) in l) <==> ((((1 + sm) as nat) - 1) as nat in s);
    assert ((((1 + sm) as nat) - 1) as nat) == sm;
    assert sm !in s;

    // all candidates smaller are in l
    forall candidate: nat | candidate < SmallestMissing(l)
      ensures candidate in l
    {
      if candidate == 0 {
        assert l[0] == 0;
      } else {
        var cprev: nat := (candidate - 1) as nat;
        assert candidate < ((1 + sm) as nat);
        assert candidate - 1 < sm;
        assert cprev < sm;
        // from auxiliary lemma on s
        assert cprev in s;
        InShiftDownTailEquiv(l, candidate);
        assert (candidate in l) <==> (((candidate - 1) as nat) in s);
        assert ((candidate - 1) as nat) == cprev;
        assert ((candidate - 1) as nat) in s;
        assert candidate in l;
      }
    }
  }
}
// </vc-helpers>

// <vc-spec>
function SmallestMissing(l: seq<nat>): nat

lemma SmallestMissingSpecSatisfied(l: seq<nat>)
    requires forall i, j :: 0 <= i < j < |l| ==> l[i] < l[j]
    ensures SmallestMissing(l) !in l
    ensures forall candidate: nat :: candidate < SmallestMissing(l) ==> candidate in l
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): delegate proof to auxiliary lemma */
  SmallestMissingSpecSatisfiedAux(l);
}
// </vc-code>
