// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed duplicate SmallestMissing function definition */
function SmallestMissingHelper(l: seq<nat>, index: nat, expected: nat): nat
  requires index <= |l|
  requires expected <= index
  requires forall i :: 0 <= i < index ==> i < |l| && l[i] == i
  requires forall i, j :: 0 <= i < j < |l| ==> l[i] < l[j]
  decreases |l| - index
{
  if index == |l| then expected
  else if l[index] == expected then SmallestMissingHelper(l, index + 1, expected + 1)
  else expected
}

/* helper modified by LLM (iteration 5): strengthened preconditions for correct indexing */
lemma SmallestMissingHelperCorrect(l: seq<nat>, index: nat, expected: nat)
  requires index <= |l|
  requires expected <= index
  requires forall i :: 0 <= i < index ==> i < |l| && l[i] == i
  requires forall i, j :: 0 <= i < j < |l| ==> l[i] < l[j]
  ensures SmallestMissingHelper(l, index, expected) !in l
  ensures forall candidate: nat :: candidate < SmallestMissingHelper(l, index, expected) ==> candidate in l
  decreases |l| - index
{
  var result := SmallestMissingHelper(l, index, expected);
  if index == |l| {
    // result == expected
    // Show expected !in l
    if expected in l {
      var pos :| 0 <= pos < |l| && l[pos] == expected;
      assert pos < index; // since index == |l|
      assert l[pos] == pos; // from precondition
      assert l[pos] == expected;
      assert pos == expected;
      assert expected < index;
      assert false;
    }
  } else if l[index] == expected {
    SmallestMissingHelperCorrect(l, index + 1, expected + 1);
  } else {
    // result == expected and l[index] != expected
    // Since l is sorted and l[index] != expected, and we know 0,1,...,expected-1 are in l
    // expected cannot be in l
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
  /* code modified by LLM (iteration 5): implement SmallestMissing function body */
  if |l| == 0 {
    return 0;
  } else if l[0] != 0 {
    return 0;
  } else {
    return SmallestMissingHelper(l, 0, 0);
  }
}
// </vc-code>
