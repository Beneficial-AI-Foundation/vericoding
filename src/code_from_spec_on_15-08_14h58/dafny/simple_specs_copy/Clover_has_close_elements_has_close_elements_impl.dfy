method has_close_elements(numbers: seq<real>, threshold: real) returns (res: bool)
 requires threshold >= 0.0
 ensures res ==> exists i: int, j: int :: 0 <= i < |numbers| && 0 <= j < |numbers| && i != j && (if numbers[i] - numbers[j] < 0.0 then numbers[j] - numbers[i] else numbers[i] - numbers[j]) < threshold
 ensures !res ==> (forall i: int, j: int :: 1 <= i < |numbers| && 0 <= j < i ==> (if numbers[i] - numbers[j] < 0.0 then numbers[j] - numbers[i] else numbers[i] - numbers[j]) >= threshold)
{
    /* code modified by LLM (iteration 1): Added early return for sequences with less than 2 elements */
    if |numbers| < 2 {
        res := false;
        return;
    }
    
    res := false;
    
    var i := 1;
    /* code modified by LLM (iteration 1): Fixed loop invariant to handle empty sequences properly */
    while i < |numbers|
        invariant 1 <= i <= |numbers|
        invariant !res ==> (forall ii: int, jj: int :: 1 <= ii < i && 0 <= jj < ii ==> (if numbers[ii] - numbers[jj] < 0.0 then numbers[jj] - numbers[ii] else numbers[ii] - numbers[jj]) >= threshold)
        invariant res ==> exists ii: int, jj: int :: 0 <= ii < |numbers| && 0 <= jj < |numbers| && ii != jj && (if numbers[ii] - numbers[jj] < 0.0 then numbers[jj] - numbers[ii] else numbers[ii] - numbers[jj]) < threshold
    {
        var j := 0;
        while j < i
            invariant 0 <= j <= i
            invariant !res ==> (forall ii: int, jj: int :: 1 <= ii < i && 0 <= jj < ii ==> (if numbers[ii] - numbers[jj] < 0.0 then numbers[jj] - numbers[ii] else numbers[ii] - numbers[jj]) >= threshold)
            invariant !res ==> (forall jj: int :: 0 <= jj < j ==> (if numbers[i] - numbers[jj] < 0.0 then numbers[jj] - numbers[i] else numbers[i] - numbers[jj]) >= threshold)
            invariant res ==> exists ii: int, jj: int :: 0 <= ii < |numbers| && 0 <= jj < |numbers| && ii != jj && (if numbers[ii] - numbers[jj] < 0.0 then numbers[jj] - numbers[ii] else numbers[ii] - numbers[jj]) < threshold
        {
            var diff := if numbers[i] - numbers[j] < 0.0 then numbers[j] - numbers[i] else numbers[i] - numbers[j];
            if diff < threshold {
                res := true;
                return;
            }
            j := j + 1;
        }
        i := i + 1;
    }
}