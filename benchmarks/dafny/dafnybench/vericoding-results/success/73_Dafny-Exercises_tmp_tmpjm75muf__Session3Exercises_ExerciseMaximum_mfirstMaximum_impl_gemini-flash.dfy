//Algorithm 1: From left to right return the first

//Algorithm 2: From right to left return the last

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method mfirstMaximum(v:array<int>) returns (i:int)
requires v.Length>0
ensures 0<=i<v.Length 
ensures forall k:: 0<=k<v.Length ==> v[i]>=v[k]
ensures forall l:: 0<=l<i ==> v[i]>v[l]
//Algorithm: from left to right
// </vc-spec>
// <vc-code>
{
    i := 0;
    var j := 1;
    while j < v.Length
        invariant 0 <= i < j <= v.Length
        invariant forall k :: 0 <= k < j ==> v[i] >= v[k]
        invariant forall l :: 0 <= l < i ==> v[i] > v[l]
    {
        if v[j] > v[i]
        {
            i := j;
        }
        else if v[j] == v[i] && j > i // This clause is technically not needed for the postcondition, but ensures 'i' moves to the rightmost equal maximum.
                                        // However, the specification for 'firstMaximum' says "from left to right return the first",
                                        // so we should only update 'i' if a strictly larger element is found.
                                        // The current code implements the "first from left" correctly without this '=='' check.
                                        // The postcondition `forall l:: 0<=l<i ==> v[i]>v[l]` ensures we pick the *first* maximum from the left.
        {
            // Do nothing, i remains the index of the first maximum seen so far.
        }
        j := j + 1;
    }
    return i;
}
// </vc-code>

//Algorithm : from left to right
//Algorithm : from right to left