// Noa Leron 207131871
// Tsuri Farhana 315016907


ghost predicate ExistsSubstring(str1: string, str2: string) {
    // string in Dafny is a sequence of characters (seq<char>) and <= on sequences is the prefix relation
    exists offset :: 0 <= offset <= |str1| && str2 <= str1[offset..]
}

ghost predicate Post(str1: string, str2: string, found: bool, i: nat) {
    (found <==> ExistsSubstring(str1, str2)) &&
    (found ==> i + |str2| <= |str1| && str2 <= str1[i..])
}

/*
Goal: Verify correctness of the following code. Once done, remove the {:verify false} (or turn it into {:verify true}).

Feel free to add GHOST code, including calls to lemmas. But DO NOT modify the specification or the original (executable) code.
*/

//this is our lemmas, invatiants and presicats


ghost predicate Outter_Inv_correctness(str1: string, str2: string, found: bool, i : nat)
{
    (found ==> (i + |str2| <= |str1| && str2 <= str1[i..])) // Second part of post condition
    &&
    (!found &&  0 < i <= |str1| && i != |str2|-1 ==> !(ExistsSubstring(str1[..i], str2))) // First part of post condition
    &&
    (!found ==> i <= |str1|)
}

ghost predicate Inner_Inv_correctness(str1: string, str2: string, i : nat, j: int, found: bool){
    0 <= j <= i && // index in range
    j < |str2| && // index in range
    i < |str1| &&// index in range
    (str1[i] == str2[j] ==> str2[j..] <= str1[i..]) &&
    (found ==> j==0 && str1[i] == str2[j])
}

ghost predicate Inner_Inv_Termination(str1: string, str2: string, i : nat, j: int, old_i: nat, old_j: nat){
    old_j - j == old_i - i
}

// <vc-helpers>
lemma PrefixEqualityImpliesPrefix(str1: string, str2: string, i: nat)
  requires i + |str2| <= |str1|
  requires forall t :: 0 <= t < |str2| ==> str1[i + t] == str2[t]
  ensures str2 <= str1[i..]
{
  var s := str1[i..];
  var k := 0;
  while k < |str2|
    invariant 0 <= k <= |str2|
    invariant forall m :: 0 <= m < k ==> s[m] == str2[m]
  {
    assert s[k] == str1[i + k];
    assert s[k] == str2[k];
    k := k + 1;
  }
  assert forall m :: 0 <= m < |str2| ==> s[m] == str2[m];
  assert s[0..|str2|] == str2;
  assert str2 <= s;
}

lemma MismatchImpliesNotPrefix(str1: string, str2: string, i: nat, j: int)
  requires 0 <= j < |str2|
  requires i + |str2| <= |str1|
  requires str1[i + j] != str2[j]
  ensures !(str2 <= str1[i..])
{
  if str2 <= str1[i..] {
    // from prefix relation we get equality of elements
    assert str1[i + j] == str2[j];
    assert false;
  }
}

lemma NoOccurrence_total(str1: string, str2: string, i: nat)
  requires |str2| > 0
  requires i <= |str1|
  requires forall k :: 0 <= k < i ==> !(str2 <= str1[k..])
  requires i + |str2| > |str1|
  ensures !(ExistsSubstring(str1, str2))
{
  if exists off :: 0 <= off <= |str1| && str2 <= str1[off..] {
    var off :| 0 <= off <= |str1| && str2 <= str1[off..];
    if off < i {
      // contradicts the first requirement
      assert !(str2 <= str1[off..]);
      assert false;
    } else {
      // off >= i. From str2 <= str1[off..] we get off + |str2| <= |str1|
      assert off + |str2| <= |str1|;
      // hence i + |str2| <= |str1|, contradicting the third requirement
      assert i + |str2| <= |str1|;
      assert false;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method FindFirstOccurrence(str1: string, str2: string) returns (found: bool, i: nat)
    ensures Post(str1, str2, found, i)
// </vc-spec>
// <vc-code>
{
  if |str2| == 0 {
    found := true;
    i := 0;
    return;
  }

  i := 0;
  found := false;
  while i + |str2| <= |str1| && !found
    invariant 0 <= i <= |str1|
    invariant forall k :: 0 <= k < i ==> !(str2 <= str1[k..])
    invariant (found ==> i + |str2| <= |str1| && str2 <= str1[i..])
    decreases |str1| - i
  {
    var old_i := i;
    var j := 0;
    // the outer loop guard guarantees i + |str2| <= |str1| at the start of the iteration
    assert i + |str2| <= |str1|;
    while j < |str2| && str1[i + j] == str2[j]
      invariant 0 <= j <= |str2|
      invariant forall t :: 0 <= t < j ==> str1[i + t] == str2[t]
      decreases |str2| - j
    {
      j := j + 1;
    }

    if j == |str2| {
      // full match found
      // prove the required prefix relation
      assert forall t :: 0 <= t < |str2| ==> str1[i + t] == str2[t];
      assert i + |str2| <= |str1|;
      PrefixEqualityImpliesPrefix(str1, str2, i);
      found := true;
    } else {
      // mismatch at position j, so position i is not a valid start
      if j < |str2| {
        assert i + |str2| <= |str1|;
        assert 0 <= j < |str2|;
        MismatchImpliesNotPrefix(str1, str2, i, j);
      }
      i := i + 1;
      assert old_i < i;
    }

    // show that if the loop would continue then the measure decreases
    assert (!found) ==> old_i < i;
    assert (!found) ==> |str1| - i < |str1| - old_i;
  }

  if found {
    // we have established the prefix relation when detecting the match
    assert 0 <= i <= |str1|;
    assert str2 <= str1[i..];
    assert exists off :: 0 <= off <= |str1| && str2 <= str1[off..];
  } else {
    // show there is no occurrence in the whole string
    if |str2| > 0 {
      assert i <= |str1|;
      // From exiting the loop with !found we know i + |str2| > |str1|
      assert i + |str2| > |str1|;
      NoOccurrence_total(str1, str2, i);
    }
  }
}
// </vc-code>

