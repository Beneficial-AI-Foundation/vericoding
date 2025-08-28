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
ghost predicate Outter_Inv_Correctness(str1: string, str2: string, found: bool, i: nat)
{
    (found ==> (i + |str2| <= |str1| && str2 <= str1[i..])) &&
    (!found ==> i <= |str1|) &&
    (!found ==> forall k :: 0 <= k < i ==> !(str2 <= str1[k..]))
}

ghost predicate Inner_Inv_Correctness(str1: string, str2: string, i: nat, j: int, found: bool)
{
    0 <= j <= |str2| &&
    i + j <= |str1| &&
    (forall k :: 0 <= k < j ==> str1[i + k] == str2[k]) &&
    (!found ==> j < |str2| || i + j == |str1|)
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method FindFirstOccurrence(str1: string, str2: string) returns (found: bool, i: nat)
    ensures Post(str1, str2, found, i)
// </vc-spec>
// </vc-spec>

// <vc-code>
method FindFirstOccurrenceImpl(str1: string, str2: string) returns (found: bool, i: nat)
    ensures Post(str1, str2, found, i)
{
    found := false;
    i := 0;
    if |str2| == 0 {
        return true, 0;
    }
    while i < |str1| && !found
        invariant Outter_Inv_Correctness(str1, str2, found, i)
        decreases |str1| - i
    {
        if str1[i] == str2[0] {
            var j := 0;
            var matched := true;
            while j < |str2| && i + j < |str1| && matched
                invariant 0 <= j <= |str2|
                invariant i + j <= |str1|
                invariant matched ==> forall k :: 0 <= k < j ==> str1[i + k] == str2[k]
                invariant Inner_Inv_Correctness(str1, str2, i, j, found)
                decreases |str2| - j
            {
                if str1[i + j] != str2[j] {
                    matched := false;
                }
                j := j + 1;
            }
            if matched && j == |str2| {
                found := true;
            }
        }
        if !found {
            i := i + 1;
        }
    }
}
// </vc-code>
