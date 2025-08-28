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
lemma ExistsSubstringPrefix(str1: string, str2: string, k: nat)
    requires k <= |str1|
    requires ExistsSubstring(str1[k..], str2)
    ensures ExistsSubstring(str1, str2)
{
    var offset :| 0 <= offset <= |str1[k..]| && str2 <= str1[k..][offset..];
    assert str1[k..][offset..] == str1[k+offset..];
    assert str2 <= str1[k+offset..];
    assert 0 <= k+offset <= |str1|;
}

lemma NoSubstringInPrefix(str1: string, str2: string, k: nat)
    requires k < |str1|
    requires forall offset :: 0 <= offset <= k ==> !(str2 <= str1[offset..])
    ensures !ExistsSubstring(str1[..k+1], str2)
{
    if ExistsSubstring(str1[..k+1], str2) {
        var offset :| 0 <= offset <= |str1[..k+1]| && str2 <= str1[..k+1][offset..];
        assert offset <= k;
        assert str1[..k+1][offset..] == str1[offset..k+1];
        assert str2 <= str1[offset..k+1];
        if |str2| <= k + 1 - offset {
            assert str2 <= str1[offset..];
            assert false;
        }
    }
}

lemma EmptyStringExists(str1: string)
    ensures ExistsSubstring(str1, "")
{
    assert "" <= str1[0..];
}

lemma NoExistsImpliesNoPrefix(str1: string, str2: string, i: nat)
    requires i <= |str1|
    requires forall k :: 0 <= k < i ==> !(str2 <= str1[k..])
    requires i > 0
    ensures !ExistsSubstring(str1[..i], str2)
{
    if ExistsSubstring(str1[..i], str2) {
        var offset :| 0 <= offset <= |str1[..i]| && str2 <= str1[..i][offset..];
        if offset < i {
            assert str1[..i][offset..] == str1[offset..i];
            if |str2| <= i - offset {
                assert str2 <= str1[offset..];
                assert false;
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method FindFirstOccurrence(str1: string, str2: string) returns (found: bool, i: nat)
    ensures Post(str1, str2, found, i)
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    if |str2| == 0 {
        return true, 0;
    }
    
    if |str1| < |str2| {
        return false, 0;
    }
    
    i := 0;
    found := false;
    
    while i <= |str1| - |str2| && !found
        invariant 0 <= i <= |str1| - |str2| + 1
        invariant !found
        invariant forall k :: 0 <= k < i ==> !(str2 <= str1[k..])
        invariant i == 0 || !ExistsSubstring(str1[..i], str2)
        decreases |str1| - |str2| - i + 1
    {
        var j := 0;
        var matches := true;
        
        while j < |str2| && matches && i + j < |str1|
            invariant 0 <= j <= |str2|
            invariant matches ==> forall k :: 0 <= k < j ==> str1[i+k] == str2[k]
            invariant matches ==> i + j <= |str1|
            invariant !matches ==> exists k :: 0 <= k < j && str1[i+k] != str2[k]
            decreases |str2| - j
        {
            if str1[i + j] != str2[j] {
                matches := false;
            } else {
                j := j + 1;
            }
        }
        
        if matches && j == |str2| {
            found := true;
            assert forall k :: 0 <= k < |str2| ==> str1[i+k] == str2[k];
            assert str2 <= str1[i..];
            return true, i;
        } else {
            assert !(str2 <= str1[i..]);
            if i > 0 {
                NoExistsImpliesNoPrefix(str1, str2, i);
            }
            i := i + 1;
        }
    }
    
    assert forall k :: 0 <= k <= |str1| - |str2| ==> !(str2 <= str1[k..]);
    assert !ExistsSubstring(str1, str2);
    return false, i;
}
// </vc-code>
