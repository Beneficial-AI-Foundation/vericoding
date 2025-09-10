predicate ValidInput(n: nat, m: nat, buttons: seq<seq<nat>>)
{
    |buttons| == n &&
    n >= 1 && m >= 1 &&
    forall i :: 0 <= i < n ==> forall j :: 0 <= j < |buttons[i]| ==> 1 <= buttons[i][j] <= m
}

function unionOfAllBulbs(buttons: seq<seq<nat>>): set<nat>
{
    set i, j | 0 <= i < |buttons| && 0 <= j < |buttons[i]| :: buttons[i][j]
}

predicate CanTurnOnAllBulbs(m: nat, buttons: seq<seq<nat>>)
{
    |unionOfAllBulbs(buttons)| == m
}

// <vc-helpers>
function SeqPrefixSet(s: seq<nat>, j: nat): set<nat>
  requires j <= |s|
  decreases j
{
  if j == 0 then {} else SeqPrefixSet(s, j-1) + { s[j-1] }
}

function PrefixButtons(buttons: seq<seq<nat>>, i: nat): set<nat>
  requires 0 <= i <= |buttons|
  decreases i
{
  if i == 0 then {} else PrefixButtons(buttons, i-1) + SeqPrefixSet(buttons[i-1], |buttons[i-1]|)
}

lemma SeqPrefixSetCons(s: seq<nat>, j: nat)
  requires j < |s|
  ensures SeqPrefixSet(s, j) + { s[j] } == SeqPrefixSet(s, j+1)
{
  assert SeqPrefixSet(s, j+1) == (if j+1 == 0 then {} else SeqPrefixSet(s, j) + { s[j] });
  assert SeqPrefixSet(s, j+1) == SeqPrefixSet(s, j) + { s[j] };
}

lemma SeqPrefixSetToComprehension(s: seq<nat>, j: nat)
  requires j <= |s|
  ensures SeqPrefixSet(s, j) == set q | 0 <= q < j :: s[q]
  decreases j
{
  if j == 0 {
    // SeqPrefixSet(s,0) == {}
  } else {
    SeqPrefixSetToComprehension(s, j-1);
    assert SeqPrefixSet(s, j) == SeqPrefixSet(s, j-1) + { s[j-1] };
    assert SeqPrefixSet(s, j-1) == set q | 0 <= q < j-1 :: s[q];
    assert SeqPrefixSet(s, j) == (set q | 0 <= q < j-1 :: s[q]) + { s[j-1] };
    assert SeqPrefixSet(s, j) == set q | 0 <= q < j :: s[q];
  }
}

lemma PrefixButtonsStep(buttons: seq<seq<nat>>, i: nat)
  requires 0 <= i < |buttons|
  ensures PrefixButtons(buttons, i) + SeqPrefixSet(buttons[i], |buttons[i]|) == PrefixButtons(buttons, i+1)
{
  assert PrefixButtons(buttons, i+1) == (if i+1 == 0 then {} else PrefixButtons(buttons, i) + SeqPrefixSet(buttons[i], |buttons[i]|));
  assert PrefixButtons(buttons, i+1) == PrefixButtons(buttons, i) + SeqPrefixSet(buttons[i], |buttons[i]|);
}

lemma PrefixButtonsCorrect(buttons: seq<seq<nat>>, i: nat)
  requires 0 <= i <= |buttons|
  ensures PrefixButtons(buttons, i) == set p,q | 0 <= p < i && 0 <= q < |buttons[p]| :: buttons[p][q]
  decreases i
{
  if i == 0 {
    // both sides are empty sets
  } else {
    PrefixButtonsCorrect(buttons, i-1);
    assert PrefixButtons(buttons, i) == PrefixButtons(buttons, i-1) + SeqPrefixSet(buttons[i-1], |buttons[i-1]|);
    SeqPrefixSetToComprehension(buttons[i-1], |buttons[i-1]|);
    assert PrefixButtons(buttons, i) == (set p,q | 0 <= p < i-1 && 0 <= q < |buttons[p]| :: buttons[p][q]) + (set q | 0 <= q < |buttons[i-1]| :: buttons[i-1][q]);
    assert PrefixButtons(buttons, i) == set p,q | 0 <= p < i && 0 <= q < |buttons[p]| :: buttons[p][q];
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: nat, m: nat, buttons: seq<seq<nat>>) returns (result: string)
    requires ValidInput(n, m, buttons)
    ensures result == "YES" || result == "NO"
    ensures result == "YES" <==> CanTurnOnAllBulbs(m, buttons)
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var s: set<int> := {};
  while i < n
    invariant 0 <= i <= n
    invariant s == PrefixButtons(buttons, i)
    decreases n - i
  {
    var j := 0;
    while j < |buttons[i]|
      invariant 0 <= j <= |buttons[i]|
      invariant s == PrefixButtons(buttons, i) + SeqPrefixSet(buttons[i], j)
      decreases |buttons[i]| - j
    {
      // By the inner invariant, adding the current button's bulb updates the SeqPrefixSet by one element
      s := s + { buttons[i][j] };
      // Use lemma to update the SeqPrefixSet part of the invariant
      SeqPrefixSetCons(buttons[i], j);
      assert s == PrefixButtons(buttons, i) + SeqPrefixSet(buttons[i], j+1);
      j := j + 1;
    }
    // After finishing inner loop, j == |buttons[i]| and invariant gives s == PrefixButtons(buttons,i) + SeqPrefixSet(buttons[i], |buttons[i]|)
    // Use lemma to fold this into PrefixButtons(buttons, i+1)
    PrefixButtonsStep(buttons, i);
    i := i + 1;
  }

  // Now i == n and outer invariant gives s == PrefixButtons(buttons, n)
  // Relate PrefixButtons to unionOfAllBulbs
  PrefixButtonsCorrect(buttons, n);
  assert s == unionOfAllBulbs(buttons);

  if |s| == m {
    result := "YES";
  } else {
    result := "NO";
  }

  assert (result == "YES") <==> (|s| == m);
  assert (|s| == m) <==> (|unionOfAllBulbs(buttons)| == m);
}
// </vc-code>

