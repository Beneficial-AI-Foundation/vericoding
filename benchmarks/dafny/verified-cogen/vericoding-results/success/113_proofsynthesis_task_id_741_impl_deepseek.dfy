// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma AllSameLemma(char_arr: array<char>, i: int)
    requires 0 <= i < char_arr.Length
    requires forall j :: 1 <= j <= i ==> char_arr[0] == char_arr[j]
    ensures char_arr[0] == char_arr[i]
{
    // The proof follows from the precondition
}
// </vc-helpers>

// <vc-spec>
method AllCharactersSame(char_arr: array<char>) returns (result: bool)
    ensures result == (forall i :: 1 <= i < char_arr.Length ==> char_arr[0] == char_arr[i])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fixed while loop invariant and termination */
{
    if char_arr.Length == 0 {
        result := true;
        return;
    }
    
    var index := 1;
    while index < char_arr.Length
        invariant 1 <= index <= char_arr.Length
        invariant forall j :: 1 <= j < index ==> char_arr[0] == char_arr[j]
    {
        if char_arr[index] != char_arr[0] {
            result := false;
            return;
        }
        index := index + 1;
    }
    
    result := true;
}
// </vc-code>
