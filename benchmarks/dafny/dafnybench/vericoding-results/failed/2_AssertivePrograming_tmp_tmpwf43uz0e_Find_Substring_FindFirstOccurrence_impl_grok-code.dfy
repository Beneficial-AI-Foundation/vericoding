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
ghost predicate Inv(str1: string, str2: string, outer_i: nat)
{
  forall k : nat :: 0 <= k < outer_i ==> !(str2 <= str1[k..])
}

lemma NotExistsIfInvariantHolds(str1: string, str2: string, outer_i:nat)
requires Inv(str1, str2, outer_i) && outer_i > |str1| - |str2|
ensures !ExistsSubstring(str1, str2)
{
  if exists offset :: 0 <= offset < |str1| && offset + |str2| <= |str1| && str2 <= str1[offset..] {
    var offset :| 0 <= offset < |str1| && offset + |str2| <= |str1| && str2 <= str1[offset..];
    if offset < outer_i {
      assert Inv(str1, str2, outer_i);
      assert !(str2 <= str1[offset..]);  // contradiction
    } else {
      assert false;  // impossible since offset <= |str1| - |str2| < outer_i
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
    assert ExistsSubstring(str1, str2);
    return true, 0;
  } else if |str2| > |str1| {
    assert !ExistsSubstring(str1, str2);
    return false, |str1|;
  } else {
    var outer_i := 0;
    while outer_i <= |str1| - |str2|
      invariant Inv(str1, str2, outer_i)
    {
      var j: nat := 0;
      while j < |str2| && str1[outer_i + j] == str2[j]
        invariant 0 <= j <= |str2| && (forall m : nat :: 0 <= m < j ==> str1[outer_i + m] == str2[m])
      {
        j := j + 1;
      }
      if j == |str2| {
        assert forall p : nat :: 0 <= p < |str2| ==> str2[p] == str1[outer_i + p];
        assert str2 == str1[outer_i..outer_i + |str2|];
        assert str2 <= str1[outer_i..];
        assert ExistsSubstring(str1, str2);
        return true, outer_i;
      }
      outer_i := outer_i + 1;
    }
    NotExistsIfInvariantHolds(str1, str2, outer_i);
    assert !ExistsSubstring(str1, str2);
    return false, |str1| - |str2| + 1;
  }
}
// </vc-code>

