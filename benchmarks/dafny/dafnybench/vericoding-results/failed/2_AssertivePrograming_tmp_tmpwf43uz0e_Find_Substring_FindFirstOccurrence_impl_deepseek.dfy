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
lemma ExistsSubstringImplies(str1: string, str2: string, offset: nat)
    requires 0 <= offset <= |str1|
    requires str2 <= str1[offset..]
    ensures ExistsSubstring(str1, str2)
{
}

lemma NotExistsSubstringImplies(str1: string, str2: string, i: nat)
    requires i <= |str1|
    requires forall offset :: 0 <= offset < i ==> !(str2 <= str1[offset..])
    ensures !ExistsSubstring(str1[..i], str2)
{
}

lemma PrefixLemma(s1: string, s2: string, i: nat, j: nat)
    requires j <= |s2|
    requires s2[j..] <= s1[i..]
    requires s1[i] == s2[j]
    ensures s2[j..] <= s1[i..]
{
}

lemma EmptyStringLemma(s: string)
    ensures "" <= s
{
}
// </vc-helpers>

// <vc-spec>
method FindFirstOccurrence(str1: string, str2: string) returns (found: bool, i: nat)
    ensures Post(str1, str2, found, i)
// </vc-spec>
// <vc-code>
{
    found := false;
    i := 0;
    
    while i <= |str1| - |str2| && !found
        invariant i <= |str1|
        invariant !found ==> forall offset :: 0 <= offset < i ==> !(str2 <= str1[offset..])
        invariant found ==> str2 <= str1[i..] && i + |str2| <= |str1|
    {
        var j: int := 0;
        var match: bool := true;
        
        while j < |str2| && match
            invariant 0 <= j <= |str2|
            invariant forall k :: 0 <= k < j ==> str1[i + k] == str2[k]
            invariant match == (j < |str2| ==> str1[i + j] == str2[j])
        {
            if str1[i + j] != str2[j] {
                match := false;
            } else {
                j := j + 1;
            }
        }
        
        if match && j == |str2| {
            found := true;
        } else {
            i := i + 1;
        }
    }
    
    if !found {
        i := 0;
    }
}
// </vc-code>

