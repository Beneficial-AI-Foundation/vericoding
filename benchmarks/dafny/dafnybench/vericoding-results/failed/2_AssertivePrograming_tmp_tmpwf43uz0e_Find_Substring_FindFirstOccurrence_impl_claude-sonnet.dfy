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
lemma ExistsSubstringAtOffset(str1: string, str2: string, offset: nat)
    requires 0 <= offset <= |str1|
    requires str2 <= str1[offset..]
    ensures ExistsSubstring(str1, str2)
{
    // The witness for ExistsSubstring is offset
}

lemma NoSubstringPrefix(str1: string, str2: string, prefix_len: nat)
    requires 0 < prefix_len <= |str1|
    requires |str2| > 0
    requires forall k :: 0 <= k < prefix_len ==> !(str2 <= str1[k..])
    ensures !ExistsSubstring(str1[..prefix_len], str2)
{
    if ExistsSubstring(str1[..prefix_len], str2) {
        var offset :| 0 <= offset <= |str1[..prefix_len]| && str2 <= str1[..prefix_len][offset..];
        assert offset < prefix_len;
        assert str1[..prefix_len][offset..] == str1[offset..prefix_len];
        assert str2 <= str1[offset..];
        assert false;
    }
}

lemma PrefixProperty(str1: string, str2: string, i: nat)
    requires i <= |str1|
    requires !ExistsSubstring(str1[..i], str2)
    requires |str2| > 0
    ensures forall k :: 0 <= k < i ==> !(str2 <= str1[k..])
{
    forall k | 0 <= k < i
        ensures !(str2 <= str1[k..])
    {
        if str2 <= str1[k..] {
            assert str1[..i][k..] == str1[k..i];
            assert str2 <= str1[k..i];
            assert ExistsSubstring(str1[..i], str2);
            assert false;
        }
    }
}

lemma StrMatchComplete(str1: string, str2: string, i: nat)
    requires i + |str2| <= |str1|
    requires forall k :: 0 <= k < |str2| ==> str1[i + k] == str2[k]
    ensures str2 <= str1[i..]
{
    // When all characters match, we have a substring match
}

lemma NoSubstringImpliesNoExists(str1: string, str2: string, i: nat)
    requires |str2| > 0
    requires i > |str1| - |str2|
    requires forall k :: 0 <= k < i ==> !(str2 <= str1[k..])
    ensures !ExistsSubstring(str1, str2)
{
    if ExistsSubstring(str1, str2) {
        var offset :| 0 <= offset <= |str1| && str2 <= str1[offset..];
        if offset < i {
            assert str2 <= str1[offset..];
            assert !(str2 <= str1[offset..]);
            assert false;
        } else {
            assert i <= offset <= |str1|;
            assert str2 <= str1[offset..];
            assert |str2| <= |str1[offset..]| == |str1| - offset <= |str1| - i;
            assert |str2| <= |str1| - i < |str2|;
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
        return true, 0;
    }
    
    if |str1| < |str2| {
        return false, 0;
    }
    
    found := false;
    i := 0;
    
    while i <= |str1| - |str2| && !found
        invariant 0 <= i <= |str1| - |str2| + 1
        invariant found ==> (i + |str2| <= |str1| && str2 <= str1[i..])
        invariant !found ==> forall k :: 0 <= k < i ==> !(str2 <= str1[k..])
        decreases |str1| - |str2| + 1 - i
    {
        var j := 0;
        var isMatch := true;
        
        while j < |str2| && isMatch
            invariant 0 <= j <= |str2|
            invariant isMatch ==> (i + j <= |str1| && forall k :: 0 <= k < j ==> str1[i + k] == str2[k])
            invariant !isMatch ==> (i + j > |str1| || exists k :: 0 <= k < j && str1[i + k] != str2[k])
            decreases |str2| - j
        {
            if i + j >= |str1| {
                isMatch := false;
            } else if str1[i + j] != str2[j] {
                isMatch := false;
            } else {
                j := j + 1;
            }
        }
        
        if isMatch && j == |str2| {
            found := true;
            StrMatchComplete(str1, str2, i);
            ExistsSubstringAtOffset(str1, str2, i);
        } else {
            i := i + 1;
        }
    }
    
    if !found {
        NoSubstringImpliesNoExists(str1, str2, i);
        i := 0;
    }
}
// </vc-code>

