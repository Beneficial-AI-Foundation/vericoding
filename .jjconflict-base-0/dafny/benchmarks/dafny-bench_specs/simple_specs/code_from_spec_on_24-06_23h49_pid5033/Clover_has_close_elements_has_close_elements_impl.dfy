//IMPL 
method has_close_elements(numbers: seq<real>, threshold: real) returns (res: bool)
 requires threshold >= 0.0
 ensures res ==> exists i: int, j: int :: 0 <= i < |numbers| && 0 <= j < |numbers| && i != j && (if numbers[i] - numbers[j] < 0.0 then numbers[j] - numbers[i] else numbers[i] - numbers[j]) < threshold
 ensures !res ==> (forall i: int, j: int :: 1 <= i < |numbers| && 0 <= j < i ==> (if numbers[i] - numbers[j] < 0.0 then numbers[j] - numbers[i] else numbers[i] - numbers[j]) >= threshold)
{
    res := false;
    var i := 1;
    while i < |numbers|
        invariant 1 <= i <= |numbers|
        /* code modified by LLM (iteration 4): maintain invariant for all checked pairs in upper triangle */
        invariant !res ==> (forall ii: int, jj: int :: 1 <= ii < i && 0 <= jj < ii ==> (if numbers[ii] - numbers[jj] < 0.0 then numbers[jj] - numbers[ii] else numbers[ii] - numbers[jj]) >= threshold)
        /* code modified by LLM (iteration 4): if res is true, we found close elements */
        invariant res ==> exists ii: int, jj: int :: 0 <= ii < |numbers| && 0 <= jj < |numbers| && ii != jj && (if numbers[ii] - numbers[jj] < 0.0 then numbers[jj] - numbers[ii] else numbers[ii] - numbers[jj]) < threshold
    {
        var j := 0;
        while j < i
            invariant 0 <= j <= i
            invariant 1 <= i < |numbers|
            /* code modified by LLM (iteration 4): preserve outer loop invariant */
            invariant !res ==> (forall ii: int, jj: int :: 1 <= ii < i && 0 <= jj < ii ==> (if numbers[ii] - numbers[jj] < 0.0 then numbers[jj] - numbers[ii] else numbers[ii] - numbers[jj]) >= threshold)
            /* code modified by LLM (iteration 4): track progress in current row */
            invariant !res ==> (forall jj: int :: 0 <= jj < j ==> (if numbers[i] - numbers[jj] < 0.0 then numbers[jj] - numbers[i] else numbers[i] - numbers[jj]) >= threshold)
            /* code modified by LLM (iteration 4): preserve found result invariant */
            invariant res ==> exists ii: int, jj: int :: 0 <= ii < |numbers| && 0 <= jj < |numbers| && ii != jj && (if numbers[ii] - numbers[jj] < 0.0 then numbers[jj] - numbers[ii] else numbers[ii] - numbers[jj]) < threshold
        {
            var distance := if numbers[i] - numbers[j] < 0.0 then numbers[j] - numbers[i] else numbers[i] - numbers[j];
            if distance < threshold {
                res := true;
                /* code modified by LLM (iteration 4): establish postcondition witness */
                assert 0 <= i < |numbers| && 0 <= j < |numbers| && i != j;
                assert distance == (if numbers[i] - numbers[j] < 0.0 then numbers[j] - numbers[i] else numbers[i] - numbers[j]);
                assert distance < threshold;
                return;
            }
            j := j + 1;
        }
        /* code modified by LLM (iteration 4): help establish invariant after inner loop */
        assert !res ==> (forall jj: int :: 0 <= jj < i ==> (if numbers[i] - numbers[jj] < 0.0 then numbers[jj] - numbers[i] else numbers[i] - numbers[jj]) >= threshold);
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 4): final postcondition establishment */
    assert !res;
    assert i == |numbers|;
    assert forall ii: int, jj: int :: 1 <= ii < |numbers| && 0 <= jj < ii ==> (if numbers[ii] - numbers[jj] < 0.0 then numbers[jj] - numbers[ii] else numbers[ii] - numbers[jj]) >= threshold;
}