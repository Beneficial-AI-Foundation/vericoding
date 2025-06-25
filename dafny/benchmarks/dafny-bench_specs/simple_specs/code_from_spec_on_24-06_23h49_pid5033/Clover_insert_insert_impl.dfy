//IMPL 
method insert(line:array<char>, l:int, nl:array<char>, p:int, at:int)
 requires 0 <= l+p <= line.Length
 requires 0 <= p <= nl.Length
 requires 0 <= at <= l
 modifies line
 ensures forall i :: (0<=i<p) ==> line[at+i] == nl[i]
 ensures forall i :: (0<=i<at) ==> line[i] == old(line[i])
 ensures forall i :: (at+p<=i<l+p) ==> line[i] == old(line[i-p])
{
    /* code modified by LLM (iteration 1): Fixed shifting phase with correct loop direction and bounds */
    // First, shift the existing content to the right to make space
    // We need to go from right to left to avoid overwriting data we haven't moved yet
    var j := l - 1;
    while j >= at
        invariant at - 1 <= j < l
        invariant forall i :: (j+1 <= i < l) ==> line[i+p] == old(line[i])
        invariant forall i :: (0 <= i < at) ==> line[i] == old(line[i])
        invariant forall i :: (l <= i < line.Length) ==> line[i] == old(line[i])
        decreases j - at + 1
    {
        line[j + p] := line[j];
        j := j - 1;
    }
    
    /* code modified by LLM (iteration 1): Fixed insertion phase with proper invariants */
    // Then, copy the new characters from nl to the insertion point
    var k := 0;
    while k < p
        invariant 0 <= k <= p
        invariant forall i :: (0 <= i < k) ==> line[at+i] == nl[i]
        invariant forall i :: (0 <= i < at) ==> line[i] == old(line[i])
        invariant forall i :: (at+p <= i < l+p) ==> line[i] == old(line[i-p])
        invariant forall i :: (k <= i < p) ==> line[at+i] == old(line[at+i-p])
        decreases p - k
    {
        line[at + k] := nl[k];
        k := k + 1;
    }
}