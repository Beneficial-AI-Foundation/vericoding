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
ghost method Lemma_PostCondition(str1: string, str2: string, found: bool, i: nat, old_found: bool, old_i: nat)
    requires Post(str1[..old_i], str2, old_found, old_i)
    requires i == old_i - 1
    requires !old_found && i >= 0
    ensures Post(str1[..i], str2, found, i)
{
    if found {
        assert ExistsSubstring(str1[..i], str2);
        assert i + |str2| <= |str1[..i]| && str2 <= str1[..i][i..];
    } else {
        if ExistsSubstring(str1[..i], str2) {
            var offset :| 0 <= offset <= |str1[..i]| && str2 <= str1[..i][offset..];
            assert str2 <= str1[offset..];
            assert str2 <= str1[..old_i][offset..];
            assert ExistsSubstring(str1[..old_i], str2);
            assert old_found;
        }
    }
}

ghost method Lemma_InnerLoop(str1: string, str2: string, i: nat, j: nat, found: bool)
    requires Inner_Inv_correctness(str1, str2, i, j, found)
    ensures str2[j..] <= str1[i..]
{
    if j < |str2| {
        assert str1[i] == str2[j];
        if j + 1 < |str2| && i + 1 < |str1| {
            calc {
                str2[j..];
                [str2[j]] + str2[j+1..];
                { assert str1[i] == str2[j]; }
                [str1[i]] + str2[j+1..];
                { Lemma_InnerLoop(str1, str2, i+1, j+1, found); }
                [str1[i]] + str1[i+1..];
                str1[i..];
            }
        }
    }
}

ghost method Lemma_Maintenance(str1: string, str2: string, i: nat, found: bool)
    requires !found
    requires 0 <= i <= |str1| - |str2|
    requires !ExistsSubstring(str1[..i], str2)
    ensures !ExistsSubstring(str1[..i+1], str2) || (str1[i] == str2[0] && str2 <= str1[i..])
{
    if ExistsSubstring(str1[..i+1], str2) {
        var offset :| 0 <= offset <= |str1[..i+1]| && str2 <= str1[..i+1][offset..];
        if offset < i {
            assert str2 <= str1[..i][offset..];
            assert ExistsSubstring(str1[..i], str2);
        } else {
            assert offset == i;
            assert str2 <= str1[i..];
            assert str1[i] == str2[0];
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
        var i := 0;
        while i <= |str1| - |str2|
            invariant !found ==> i <= |str1|
            invariant found ==> i + |str2| <= |str1| && str2 <= str1[i..]
            invariant !found && 0 < i ==> !ExistsSubstring(str1[..i], str2)
        {
            if str1[i] == str2[0] {
                var j := 0;
                var foundInLine := false;
                while j < |str2| && i + j < |str1|
                    invariant 0 <= j <= |str2|
                    invariant i + j <= |str1|
                    invariant str2[..j] <= str1[i..i+j]
                    invariant foundInLine ==> j == |str2|
                {
                    if str1[i + j] != str2[j] {
                        break;
                    }
                    if j == |str2| - 1 {
                        foundInLine := true;
                        found := true;
                        return true, i;
                    }
                    j := j + 1;
                }
                Lemma_Maintenance(str1, str2, i, found);
            }
            i := i + 1;
        }
        return false, 0;
    }
// </vc-code>

