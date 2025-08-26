lemma EmptyStringLemma(str1: string)
    ensures ExistsSubstring(str1, "")
{
    assert "" <= str1[0..];
}

lemma NoSubstringWhenTooShort(str1: string, str2: string)
    requires |str1| < |str2|
    requires |str2| > 0
    ensures !ExistsSubstring(str1, str2)
{
    if ExistsSubstring(str1, str2) {
        var offset :| 0 <= offset <= |str1| && str2 <= str1[offset..];
        assert |str1[offset..]| == |str1| - offset;
        assert |str2| <= |str1[offset..]|;
        assert |str2| <= |str1| - offset;
        assert |str2| <= |str1|;
        assert false;
    }
}

lemma FoundImpliesExists(str1: string, str2: string, i: nat)
    requires i + |str2| <= |str1|
    requires str2 <= str1[i..]
    ensures ExistsSubstring(str1, str2)
{
    assert str2 <= str1[i..];
}

lemma CompleteSearchLemma(str1: string, str2: string, i: nat)
    requires |str2| > 0
    requires i > |str1| - |str2|
    requires forall k :: 0 <= k < i ==> !ExistsAtPosition(str1, str2, k)
    ensures !ExistsSubstring(str1, str2)
{
    if ExistsSubstring(str1, str2) {
        var offset :| 0 <= offset <= |str1| && str2 <= str1[offset..];
        if offset + |str2| <= |str1| {
            assert offset <= |str1| - |str2|;
            assert offset < i;
            assert ExistsAtPosition(str1, str2, offset);
            assert false;
        } else {
            assert |str1[offset..]| < |str2|;
            assert !(str2 <= str1[offset..]);
            assert false;
        }
    }
}

ghost predicate ExistsAtPosition(str1: string, str2: string, pos: nat) {
    pos <= |str1| && str2 <= str1[pos..]
}
</vc-helpers>

// <vc-spec>
method FindFirstOccurrence(str1: string, str2: string) returns (found: bool, i: nat)
    ensures Post(str1, str2, found, i)
// </vc-spec>
// <vc-code>
{
    if |str2| == 0 {
        EmptyStringLemma(str1);
        return true, 0;
    }
    
    if |str1| < |str2| {
        NoSubstringWhenTooShort(str1, str2);
        return false, 0;
    }
    
    found := false;
    i := 0;
    var pos := 0;
    
    while pos <= |str1| - |str2| && !found
        invariant 0 <= pos <= |str1| - |str2| + 1
        invariant Outter_Inv_correctness(str1, str2, found, i)
        invariant !found ==> forall k :: 0 <= k < pos ==> !ExistsAtPosition(str1, str2, k)
        invariant !found ==> i == pos
        invariant found ==> (i + |str2| <= |str1| && str2 <= str1[i..])
        decreases |str1| - pos
    {
        var j := 0;
        var curr_pos := pos;
        
        while curr_pos < |str1| && j < |str2| && str1[curr_pos] == str2[j]
            invariant 0 <= j <= |str2|
            invariant curr_pos == pos + j
            invariant curr_pos <= |str1|
            invariant j > 0 ==> str2[..j] <= str1[pos..]
            decreases |str2| - j
        {
            curr_pos := curr_pos + 1;
            j := j + 1;
        }
        
        if j == |str2| {
            found := true;
            i := pos;
            FoundImpliesExists(str1, str2, i);
        } else {
            assert !ExistsAtPosition(str1, str2, pos);
            pos := pos + 1;
        }
    }
    
    if !found {
        CompleteSearchLemma(str1, str2, pos);
        i := 0;
    }
}
// </vc-code>

//this is our lemmas, invatiants and presicats


ghost predicate Outter_Inv_correctness(str1: string, str2: string, found: bool, i : nat)
{
    (found ==> (i + |str2| <= |str1| && str2 <= str1[i..])) // Second part of post condition
    &&
    (!found ==> i <= |str1| - |str2| + 1)
}

ghost predicate Inner_Inv_correctness(str1: string, str2: string, i : nat, j: int, found: bool){
    0 <= j <= |str2| && // index in range
    i >= j && // index in range
    (!found ==> i < |str1| && j < |str2|) // index in range when not found
}

ghost predicate Inner_Inv_Termination(str1: string, str2: string, i : nat, j: int, old_i: nat, old_j: nat){
    old_j - j == old_i - i
}

lemma Lemma1 (str1: string, str2: string, i : nat, j: int, old_i: nat, old_j: nat, found: bool)
// requires old_j - j == old_i - i;
requires !found
requires |str2| > 0
requires Outter_Inv_correctness(str1, str2, found, old_i)
requires i+|str2|-j == old_i + 1
requires old_i+1 >= |str2|
requires old_i+1 <= |str1|
requires 0 <= i < |str1| && 0 <= j < |str2|
requires str1[i] != str2[j]
requires |str2| > 0
requires 0 < old_i <= |str1| ==> !(ExistsSubstring(str1[..old_i], str2))
ensures 0 < old_i+1 <= |str1| ==> !(ExistsSubstring(str1[..old_i+1], str2))
{
    assert  |str1[old_i+1 - |str2|..old_i+1]| == |str2|;
    assert str1[old_i+1 - |str2|..old_i+1] != str2;
    assert !(str2 <= str1[old_i+1 - |str2|..old_i+1]);
    assert 0 <= old_i < old_i+1 <= |str1|;
    assert old_i+1 >= |str2|;


    calc{
        0 < old_i+1 <= |str1| 
        && (ExistsSubstring(str1[..old_i+1], str2))
        && !(str2 <= str1[old_i+1 - |str2|..old_i+1]);
        ==>
        (!(ExistsSubstring(str1[..old_i], str2)))
        && (ExistsSubstring(str1[..old_i+1], str2))
        && !(str2 <= str1[old_i+1 - |str2|..old_i+1]);
        ==> {Lemma2(str1, str2, old_i, found);}
        ((0 < old_i < old_i+1 <= |str1| && old_i != |str2|-1) ==> 
        (|str1[old_i+1 - |str2|..old_i+1]| == |str2|) && (str2 <= str1[old_i+1 - |str2| .. old_i+1]))
        && !(str2 <= str1[old_i+1 - |str2|..old_i+1]);
        ==>
        ((0 < old_i < old_i+1 <= |str1| && old_i != |str2|-1) ==> false);
    }
}


lemma Lemma2 (str1: string, str2: string, i : nat, found: bool)
requires 0 <= i < |str1|
requires 0 < |str2| <= i+1
requires !ExistsSubstring(str1[..i], str2)
requires ExistsSubstring(str1[..i+1], str2)
ensures str2 <= str1[i+1 - |str2| .. i+1]
{

    assert exists offset :: 0 <= offset <= i+1 && str2 <= str1[offset..i+1] 
    && ((offset <= i) || (offset == i+1));

    calc{
        (0 < |str2|) 
        && (!exists offset :: 0 <= offset <= i && str2 <= str1[offset..i])
        && (exists offset :: 0 <= offset <= i+1 && str2 <= str1[offset..i+1]);
        ==>
        (0 < |str2|) 
        && (forall offset :: 0 <= offset <= i ==> !(str2 <= str1[offset..i]))
        && (exists offset :: 0 <= offset <= i+1 && str2 <= str1[offset..i+1]);
        ==>
        (0 < |str2|) 
        && (exists offset :: (0 <= offset <= i+1) && (str2 <= str1[offset..i+1]) 
        && (forall offset :: 0 <= offset <= i+1 ==>
            (offset <= i ==> !(str2 <= str1[offset..i]))));
        ==> {Lemma3(str1, str2, i);}
        (0 < |str2|) 
        && (exists offset :: (0 <= offset <= i+1) && (str2 <= str1[offset..i+1]) 
        && (offset <= i ==> !(str2 <= str1[offset..i])));
        ==>
        (0 < |str2|) 
        && (exists offset :: (0 <= offset <= i+1) && (str2 <= str1[offset..i+1]) 
        && (offset <= i ==> !(str2 <= str1[offset..i])) && (offset == i+1 ==> |str2| == 0));
        ==>
        (0 < |str2|) 
        && (exists offset :: (0 <= offset <= i+1) && (str2 <= str1[offset..i+1]) 
        && (offset <= i ==> !(str2 <= str1[offset..i])) && (offset == i+1 ==> |str2| == 0) && (offset != i+1));
        ==>
        (0 < |str2|) 
        && (exists offset :: (0 <= offset <= i+1) && (str2 <= str1[offset..i+1]) 
        && (offset <= i ==> !(str2 <= str1[offset..i])) && (offset <= i));
        ==>
        (0 < |str2|) 
        && (exists offset :: (0 <= offset <= i+1) && (str2 <= str1[offset..i+1]) 
        && !(str2 <= str1[offset..i]));
        ==>
        str2 <= str1[i+1 - |str2| .. i+1];
    }



}

lemma Lemma3(str1: string, str2: string, i : nat)
    requires 0 <= i < |str1|
    requires 0 < |str2| <= i+1
    requires exists offset :: (0 <= offset <= i+1) && str2 <= str1[offset..i+1]
    requires forall offset :: 0 <= offset <= i+1 ==> (offset <= i ==> !(str2 <= str1[offset..i]))
    ensures exists offset :: (0 <= offset <= i+1) && (str2 <= str1[offset..i+1]) && (offset <= i ==> !(str2 <= str1[offset..i]))
{
    var offset :| (0 <= offset <= i+1) && str2 <= str1[offset..i+1];
    assert 0 <= offset <= i+1 ==> (offset <= i ==> !(str2 <= str1[offset..i])); 
}
</vc-helpers>