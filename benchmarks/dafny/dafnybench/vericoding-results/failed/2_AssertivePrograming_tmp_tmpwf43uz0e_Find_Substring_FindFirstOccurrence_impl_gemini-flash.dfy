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
lemma lemma_substring_prefix(s1: string, s2: string, offset: nat)
  requires 0 <= offset <= |s1| && s2 <= s1[offset..]
  ensures exists k :: 0 <= k <= |s1| - |s2| && s1[k..k+|s2|] == s2
{
  if |s2| == 0 {
    assert exists k :: 0 <= k <= |s1| ==> s1[k..k+|s2|] == s2; // An empty string is a prefix of any string and also a substring at any position
    return;
  }
  var k := offset;
  while k + |s2| <= |s1|
    invariant offset <= k <= |s1| - |s2| + 1
    invariant s2 <= s1[offset..]
    decreases |s1| - |s2| - k
  {
    if s1[k..k+|s2|] == s2 {
      return;
    }
    k := k + 1;
  }
}

lemma lemma_no_substring_prefix(s1: string, s2: string, len: nat)
  requires 0 <= len <= |s1|
  requires forall k :: 0 <= k <= len - |s2| ==> s1[k..k+|s2|] != s2
  ensures !ExistsSubstring(s1[..len], s2)
{
  if |s2| == 0 {
    assert !ExistsSubstring(s1[..len], s2);
    return;
  }
  if ExistsSubstring(s1[..len], s2) {
    var offset_witness : nat;
    if (exists offset' :: 0 <= offset' <= |s1[..len]| && s2 <= s1[..len][offset'..]) {
      offset_witness := (choose offset' such that 0 <= offset' <= |s1[..len]| && s2 <= s1[..len][offset'..]);
      // If such an offset exists, then s1[..len][offset_witness..offset_witness+|s2|] == s2.
      // This means s1[offset_witness..offset_witness+|s2|] == s2.
      // But we have the precondition: forall k :: 0 <= k <= len - |s2| ==> s1[k..k+|s2|] != s2.
      // Since 0 <= offset_witness <= len - |s2| must hold for s1[offset_witness..offset_witness+|s2|] to be a substring within s1[..len],
      // this leads to a contradiction.
      assert {:trigger s1[offset_witness..offset_witness+|s2|]} 0 <= offset_witness <= len - |s2| && s1[offset_witness..offset_witness+|s2|] == s2; // This is the contradiction
      // The existence requires that length of source string from offset should be at least length of substring
      // i.e., offset_witness + |s2| <= |s1[..len]|
      // which is offset_witness + |s2| <= len
      // so offset_witness <= len - |s2|
      assert false; // Contradiction
    }
  }
}
lemma lemma_prefix_implies_substring(s1: string, s2: string, offset: nat)
  requires 0 <= offset <= |s1|
  requires offset + |s2| <= |s1|
  requires s1[offset..offset+|s2|] == s2
  ensures ExistsSubstring(s1, s2)
{
  if |s2| == 0 {
    assert ExistsSubstring(s1, s2);
    return;
  }
  assert s2 <= s1[offset..]; // By definition, if s1[offset..offset+|s2|] == s2, then s2 is a prefix of s1[offset..]
}
// </vc-helpers>

// <vc-spec>
method FindFirstOccurrence(str1: string, str2: string) returns (found: bool, i: nat)
    ensures Post(str1, str2, found, i)
// </vc-spec>
// <vc-code>
{
    if |str2| == 0 {
        return true, 0;
    }

    var found_result := false;
    var current_i := 0;

    while current_i + |str2| <= |str1|
        invariant 0 <= current_i <= |str1|
        invariant !found_result ==> (forall k :: 0 <= k < current_i ==> k + |str2| <= |str1| && str1[k..k+|str2|] != str2)
        invariant found_result ==> (current_i + |str2| <= |str1| && str1[current_i..current_i+|str2|] == str2)
        decreases |str1| - current_i
    {
        var j := 0;
        var sub_match := true; // Flag to check if current substring matches
        while j < |str2|
            invariant 0 <= j <= |str2|
            invariant current_i + j <= |str1| // Ensure current_i + j is a valid index for str1
            invariant sub_match == (forall k :: 0 <= k < j ==> str1[current_i+k] == str2[k])
            invariant !found_result
            decreases |str2| - j
        {
            if current_i + j >= |str1| || str1[current_i+j] != str2[j] { // Added bounds check
                sub_match := false;
                j := |str2|; // Break inner loop
            } else {
                j := j + 1;
            }
        }

        if sub_match { // If j == |str2| AND sub_match is true
            found_result := true;
            assert current_i + |str2| <= |str1|;
            assert str1[current_i..current_i+|str2|] == str2;
            lemma_prefix_implies_substring(str1, str2, current_i);
            assert ExistsSubstring(str1, str2);
            return found_result, current_i;
        }

        current_i := current_i + 1;
    }

    assert !found_result;
    lemma_no_substring_prefix(str1, str2, current_i); // current_i is |str1| - |str2| + 1 after the loop terminates
    assert !ExistsSubstring(str1, str2);
    return false, current_i;
}
// </vc-code>

