// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): proof of SmallestMissing specification by induction on length */
lemma SmallestMissingSpecSatisfied(l: seq<nat>)
    requires forall i, j :: 0 <= i < j < |l| ==> l[i] < l[j]
    ensures SmallestMissing(l) !in l
    ensures forall candidate: nat :: candidate < SmallestMissing(l) ==> candidate in l
    decreases |l|
{
  if |l| == 0 {
    assert SmallestMissing(l) == 0;
    assert SmallestMissing(l) !in l;
    assert forall candidate: nat :: candidate < SmallestMissing(l) ==> candidate in l;
  } else if l[0] != 0 {
    assert SmallestMissing(l) == 0;
    assert SmallestMissing(l) !in l;
    assert forall candidate: nat :: candidate < SmallestMissing(l) ==> candidate in l;
  } else {
    if |l| == 1 {
      assert SmallestMissing(l) == l[0] + 1;
      assert SmallestMissing(l) !in l;
      assert forall candidate: nat :: candidate < SmallestMissing(l) ==> candidate in l;
    } else if l[1] > l[0] + 1 {
      assert SmallestMissing(l) == l[0] + 1;
      assert SmallestMissing(l) !in l;
      assert forall candidate: nat :: candidate < SmallestMissing(l) ==> candidate in l;
    } else {
      var rest := l[1..];
      assert forall i, j | 0 <= i < j < |rest| :: rest[i] < rest[j];
      SmallestMissingSpecSatisfied(rest);
      assert SmallestMissing(l) == 1 + SmallestMissing(rest);
      assert SmallestMissing(rest) !in rest;
      assert forall i | 0 <= i < |rest| :: rest[i] == l[i+1];
      assert SmallestMissing(l) !in l;
      forall candidate | candidate < SmallestMissing(l) {
        if candidate == 0 {
          assert l[0] == 0;
        } else {
          assert candidate - 1 < SmallestMissing(rest);
          assert candidate - 1 in rest;
          assert candidate in l;
        }
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
/* code modified by LLM (iteration 5): implement SmallestMissing recursively handling base and gap cases */
{
  if |l| == 0 then 0
  else if l[0] != 0 then 0
  else if |l| == 1 then l[0] + 1
  else if l[1] > l[0] + 1 then l[0] + 1
  else 1 + SmallestMissing(l[1..])
}

// </vc-code>
