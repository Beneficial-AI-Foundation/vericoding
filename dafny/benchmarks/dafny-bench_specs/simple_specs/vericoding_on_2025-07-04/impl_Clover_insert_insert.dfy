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
    /* code modified by LLM (iteration 1): Simplified approach with correct bounds and invariants */
    // First, shift existing characters to the right to make space
    if p > 0 {
        var j := l - 1;
        while j >= at
            invariant j >= at - 1
            invariant forall i :: (0<=i<at) ==> line[i] == old(line[i])
            invariant forall i :: (j+1<=i<l) ==> line[i+p] == old(line[i])
            invariant forall i :: (at<=i<=j) ==> line[i] == old(line[i])
            decreases j - at + 1
        {
            line[j + p] := line[j];
            j := j - 1;
        }
    }
    
    /* code modified by LLM (iteration 1): Insert new characters with correct invariants */
    // Now insert the new characters
    var k := 0;
    while k < p
        invariant 0 <= k <= p
        invariant forall i :: (0<=i<at) ==> line[i] == old(line[i])
        invariant forall i :: (0<=i<k) ==> line[at+i] == nl[i]
        invariant forall i :: (at+p<=i<l+p) ==> line[i] == old(line[i-p])
        decreases p - k
    {
        line[at + k] := nl[k];
        k := k + 1;
    }
}