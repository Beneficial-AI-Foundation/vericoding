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
lemma ExistsSubstringTransitive(str1: string, str2: string, i: nat)
    requires i < |str1|
    requires !ExistsSubstring(str1[..i], str2)
    requires !(i + |str2| <= |str1| && str2 <= str1[i..])
    ensures !ExistsSubstring(str1[..i+1], str2)
{
    if ExistsSubstring(str1[..i+1], str2) {
        var offset :| 0 <= offset <= |str1[..i+1]| && str2 <= str1[..i+1][offset..];
        assert |str1[..i+1]| == i + 1;
        
        if offset < i {
            assert str1[..i+1][offset..] == str1[offset..i+1];
            assert str2 <= str1[offset..i+1];
            assert |str2| <= i + 1 - offset;
            
            if |str2| <= i - offset {
                assert str1[..i][offset..] == str1[offset..i];
                assert str2 <= str1[offset..i];
                assert ExistsSubstring(str1[..i], str2);
                assert false;
            } else {
                assert |str2| == i + 1 - offset;
                assert str2 == str1[offset..i+1];
                assert offset == i + 1 - |str2|;
                
                if i + 1 >= |str2| {
                    assert offset == i + 1 - |str2|;
                    if offset == i {
                        assert i + 1 == |str2|;
                        assert str2 == str1[i..i+1];
                        assert i + |str2| == i + (i + 1 - i) == i + 1;
                        assert i + 1 <= |str1|;
                        assert i + |str2| <= |str1|;
                        assert str2 <= str1[i..];
                        assert false;
                    } else {
                        assert offset < i;
                        assert str1[..i][offset..] == str1[offset..i];
                        assert str2[..|str2|-1] <= str1[offset..i];
                        assert str2[..|str2|-1] == str1[offset..i];
                        assert ExistsSubstring(str1[..i], str2[..|str2|-1]);
                    }
                }
            }
        } else {
            assert offset == i;
            assert str1[..i+1][i..] == str1[i..i+1];
            assert str2 <= str1[i..i+1];
            assert |str2| <= 1;
            assert i + |str2| <= i + 1;
            assert i + 1 <= |str1[..i+1]|;
            assert i + |str2| <= |str1|;
            assert str2 <= str1[i..];
            assert false;
        }
    }
}

lemma FoundImpliesExists(str1: string, str2: string, i: nat)
    requires i + |str2| <= |str1|
    requires str2 <= str1[i..]
    ensures ExistsSubstring(str1, str2)
{
    assert 0 <= i <= |str1|;
    assert str2 <= str1[i..];
}

lemma NoSubstringInPrefix(str1: string, str2: string, k: nat)
    requires k <= |str1|
    requires |str2| > 0
    requires forall offset :: 0 <= offset <= k - |str2| ==> !(offset + |str2| <= |str1| && str2 <= str1[offset..])
    ensures !ExistsSubstring(str1[..k], str2)
{
    if ExistsSubstring(str1[..k], str2) {
        var offset :| 0 <= offset <= |str1[..k]| && str2 <= str1[..k][offset..];
        assert offset <= k;
        assert str1[..k][offset..] == str1[offset..k];
        assert str2 <= str1[offset..k];
        assert |str2| <= k - offset;
        assert offset <= k - |str2|;
        assert str1[offset..k] <= str1[offset..];
        assert str2 <= str1[offset..];
        assert offset + |str2| <= |str1|;
        assert false;
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
        assert str2 <= str1[0..];
        FoundImpliesExists(str1, str2, 0);
        return;
    }
    
    if |str1| < |str2| {
        found := false;
        i := 0;
        assert !ExistsSubstring(str1, str2);
        return;
    }
    
    found := false;
    i := 0;
    
    while i <= |str1| - |str2|
        invariant 0 <= i <= |str1|
        invariant !found
        invariant forall offset :: 0 <= offset < i ==> !(offset + |str2| <= |str1| && str2 <= str1[offset..])
        decreases |str1| - i
    {
        var j := 0;
        var old_i := i;
        
        while j < |str2| && i < |str1| && str1[i] == str2[j]
            invariant 0 <= j <= |str2|
            invariant old_i <= i <= |str1|
            invariant i - old_i == j
            invariant j > 0 ==> j <= |str2| && str2[..j] == str1[old_i..i]
            invariant !found
            decreases |str2| - j
        {
            i := i + 1;
            j := j + 1;
        }
        
        if j == |str2| {
            found := true;
            i := old_i;
            assert j == |str2|;
            assert old_i + j == old_i + |str2|;
            assert str2[..j] == str1[old_i..old_i + j];
            assert str2[..|str2|] == str1[old_i..old_i + |str2|];
            assert str2 == str1[old_i..old_i + |str2|];
            assert old_i + |str2| <= |str1|;
            assert str2 <= str1[i..];
            FoundImpliesExists(str1, str2, i);
            return;
        }
        
        assert !(old_i + |str2| <= |str1| && str2 <= str1[old_i..]);
        i := old_i + 1;
    }
    
    assert i > |str1| - |str2|;
    assert forall offset :: 0 <= offset <= |str1| - |str2| ==> !(offset + |str2| <= |str1| && str2 <= str1[offset..]);
    NoSubstringInPrefix(str1, str2, |str1|);
    assert !ExistsSubstring(str1, str2);
    i := 0;
}
// </vc-code>

